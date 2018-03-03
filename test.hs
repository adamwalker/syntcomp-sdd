{-# LANGUAGE RecordWildCards, FlexibleContexts, ScopedTypeVariables #-}

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Bits
import Data.Tuple.All
import Control.Monad
import Data.List
import qualified Data.Text.IO as T
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Control.Monad.State
import Data.Monoid

import Data.Attoparsec.Text
import Safe
import Options.Applicative as O

import SDD.SDD
import AAG

mapAccumLM :: Monad m => (acc -> x -> m (acc, y)) -> acc -> [x] -> m (acc, [y])
mapAccumLM _ s []     = return (s, [])
mapAccumLM f s (x:xs) = do
    (s1, x')  <- f s x
    (s2, xs') <- mapAccumLM f s1 xs
    return (s2, x' : xs')

--Compiling the AIG
makeAndMap :: [(Int, Int, Int)] -> Map Int (Int, Int)
makeAndMap = Map.fromList . map func
    where func (out, x, y) = (out, (x, y))

categorizeInputs :: [Symbol] -> [Int] -> ([Int], [Int])
categorizeInputs symbols inputs = (cont, inputs \\ cont)
    where
    cont                     = map (inputs !!) theSet
    theSet                   = map idx $ filter (isControllable . typ) symbols
    isControllable (Is Cont) = True
    isControllable _         = False

doAndGates :: SDDManager -> Map Int (Int, Int) -> Map Int SDDNode -> Int -> IO (Map Int SDDNode, SDDNode)
doAndGates m andGateInputs accum andGate = 
    case Map.lookup andGate accum of
        Just x  -> return (accum, x)
        Nothing -> do
            let varIdx   =  clearBit andGate 0
                (x, y)   =  fromJustNote "doAndGates" $ Map.lookup varIdx andGateInputs
            (accum', x)  <- doAndGates m andGateInputs accum x
            (accum'', y) <- doAndGates m andGateInputs accum' y
            res          <- conjoin x y m
            n            <- neg res m
            let finalMap =  Map.insert varIdx res (Map.insert (varIdx + 1) n accum'')
            return (finalMap, fromJustNote "doAndGates2" $ Map.lookup andGate finalMap) 

computeCube :: SDDManager -> [SDDNode] -> IO SDDNode
computeCube m nodes = do
    btrue <- managerTrue m
    foldM (\x y -> conjoin x y m) btrue nodes 

data SynthState = SynthState {
    cInputInds :: [Bool],
    uInputInds :: [Bool],

    safeRegion :: SDDNode,
    initState  :: SDDNode
}

reserveSDDVar :: MonadState Int m => m Int
reserveSDDVar = do
    idx <- get
    modify (+1)
    return idx

doLabelVar :: SDDManager -> Int -> StateT Int IO [(Int, SDDNode)]
doLabelVar m idx = do
    nextIdx <- reserveSDDVar
    sddNode <- liftIO $ managerLiteral (fromIntegral nextIdx) m
    negated <- liftIO $ neg sddNode m
    return $ [(idx, sddNode), (idx + 1, negated)]

doLatchVar :: SDDManager -> Int -> StateT Int IO ((Int, Int), [(Int, SDDNode)], SDDNode)
doLatchVar m idx = do
    currentIdx <- reserveSDDVar
    nextIdx    <- reserveSDDVar
    sddNode <- liftIO $ managerLiteral (fromIntegral currentIdx) m
    negated <- liftIO $ neg sddNode m
    let stab = [(idx, sddNode), (idx + 1, negated)]
    return ((currentIdx, nextIdx), stab, negated)

compile :: SDDManager -> [Int] -> [Int] -> [(Int, Int)] -> [(Int, Int, Int)] -> Int -> IO SynthState
compile m controllableInputs uncontrollableInputs latches ands safeIndex = do

    let andGates = map sel1 ands
        andMap   = makeAndMap ands

    bfalse        <- managerFalse m
    btrue         <- managerTrue  m

    --Create the variables
    (cInputVars, endCInputVars, uInputVars, endUInputVars, latchVars, negLatchVars, endLatchVars, latchSddInds :: [(Int, Int)]) 
        <- flip evalStateT 1 $ do

            cInputVars    <- mapM (doLabelVar m) controllableInputs
            endCInputVars <- get

            uInputVars    <- mapM (doLabelVar m) uncontrollableInputs
            endUInputVars <- get

            (latchSddInds, latchVars, negLatchVars) <- unzip3 <$> mapM (doLatchVar m . fst) latches
            endLatchVars  <- get

            return (concat cInputVars, endCInputVars, concat uInputVars, endUInputVars, concat latchVars, negLatchVars, endLatchVars, latchSddInds)

    --compute the arrays for quantification
    let allVars    = [0 .. endLatchVars - 1]
        cInputInds = flip map allVars (< endCInputVars)
        uInputInds = flip map allVars (\x -> x >= endCInputVars && x < endUInputVars)

    putStrLn $ "cInputVars: " ++ show cInputInds
    putStrLn $ "uInputVars: " ++ show uInputInds

    putStrLn $ "endLatchVars: " ++ show endLatchVars

    --create the symbol table
    let tf   = [(0, bfalse), (1, btrue)]
        im   = Map.fromList $ concat [
                tf, 
                cInputVars, 
                uInputVars, 
                latchVars
            ]

    --compile the and gates
    stab     <- fst <$> mapAccumLM (doAndGates m andMap) im andGates 

    print stab

    --get the safety condition
    let bad   = fromJustNote "compile" $ Map.lookup safeIndex stab
    safe <- neg bad m
    
    --construct the initial state
    initState <- computeCube m negLatchVars

    return $ SynthState cInputInds uInputInds safe initState

forallMultiple :: [Bool] -> SDDNode -> SDDManager -> IO SDDNode
forallMultiple vars node m = do
    nn    <- neg node m
    quant <- existsMultiple vars nn m
    neg quant m

safeCpre :: SDDManager -> SynthState -> SDDNode -> IO SDDNode
safeCpre m SynthState{..} s = do
    print "*"

    scu' <- managerTrue m --vectorCompose s trel

    scu'AndSafe <- conjoin scu' safeRegion m

    sc <- existsMultiple cInputInds scu'AndSafe m

    s <- forallMultiple uInputInds sc m

    return s

fixedPoint :: SDDManager -> SDDNode -> (SDDNode -> IO SDDNode) -> IO SDDNode
fixedPoint m start func = do
    res <- func start
    case res == start of
        True  -> return res
        False -> fixedPoint m res func 

implies :: SDDNode -> SDDNode -> SDDManager -> IO SDDNode
implies x y m = do
    nx <- neg x m
    disjoin nx y m

solveSafety :: SDDManager -> SynthState -> SDDNode -> SDDNode -> IO Bool
solveSafety m ss init safeRegion = do
    btrue         <- managerTrue m
    winningRegion <- fixedPoint m btrue (safeCpre m ss)

    impl          <- implies init winningRegion m

    return $ impl == btrue

doIt :: FilePath -> IO (Either String Bool)
doIt filename = runExceptT $ do
    contents    <- lift $ T.readFile filename
    aag@AAG{..} <- ExceptT $ return $ parseOnly aag contents

    lift $ do
        let (cInputs, uInputs) = categorizeInputs symbols inputs
            Header{..}         = header

        m <- managerCreate (fromIntegral (i + 2*l + 1)) 0

        ss@SynthState{..} <- compile m cInputs uInputs latches andGates (head outputs)
        res <- solveSafety m ss initState safeRegion
        return res

run :: FilePath -> IO ()
run f = do
    res <- doIt f
    case res of
        Left err    -> putStrLn $ "Error: " ++ err
        Right True  -> putStrLn "REALIZABLE"
        Right False -> putStrLn "UNREALIZABLE"

main = execParser opts >>= run
    where
    opts   = info (helper <*> parser) (fullDesc <> progDesc "Solve the game specified in INPUT" <> O.header "Simple SDD solver")
    parser = argument O.str (metavar "INPUT")

