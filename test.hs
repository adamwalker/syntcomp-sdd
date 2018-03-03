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

import SDD.SDD hiding (deref)
import qualified SDD.SDD as SDD (deref)
import SDD.C
import AAG

deref = SDD.deref
--deref x y = return ()

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
            ref res m

            n            <- neg res m
            ref n m

            let finalMap =  Map.insert varIdx res (Map.insert (varIdx + 1) n accum'')
            return (finalMap, fromJustNote "doAndGates2" $ Map.lookup andGate finalMap) 

computeCube :: SDDManager -> [SDDNode] -> IO SDDNode
computeCube m nodes = do
    btrue <- managerTrue m
    foldM func btrue nodes 
    where
    func accum x = do
        res <- conjoin accum x m
        ref res m
        --deref accum m
        return res

data SynthState = SynthState {
    --Variable regions that get quantified out
    cInputInds    :: [Bool], --True iff its a controllable or uncontrollable input
    uInputInds    :: [Bool],

    --SDDNodes
    safeRegion    :: SDDNode,
    initState     :: SDDNode,

    --Transition relation
    renameMap     :: [SDDLiteral],
    trel          :: SDDNode,
    nextStateInds :: [Bool]
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
    liftIO $ ref sddNode m

    negated <- liftIO $ neg sddNode m
    liftIO $ ref negated m

    return $ [(idx, sddNode), (idx + 1, negated)]

doLatchVar :: SDDManager -> (Int, Int) -> StateT Int IO ((Int, Int), [(Int, SDDNode)], SDDNode, (Int, SDDNode))
doLatchVar m (idx, updateFunc) = do
    --Reserve indices
    currentIdx <- reserveSDDVar
    nextIdx    <- reserveSDDVar

    --Create the SDD nodes for the indices
    sddNode     <- liftIO $ managerLiteral (fromIntegral currentIdx) m
    liftIO $ ref sddNode m

    sddNodeNext <- liftIO $ managerLiteral (fromIntegral nextIdx)    m
    liftIO $ ref sddNodeNext m

    --For the symbol table
    negated <- liftIO $ neg sddNode m
    liftIO $ ref negated m
    let stab = [(idx, sddNode), (idx + 1, negated)]

    --The update function
    let update = (updateFunc, sddNodeNext)

    return ((currentIdx, nextIdx), stab, negated, update)

xnor :: SDDManager -> SDDNode -> SDDNode -> IO SDDNode
xnor m x y = do

    notX <- neg x m
    ref notX m

    notY <- neg y m
    ref notY m

    a <- conjoin x y m
    ref a m

    b <- conjoin notX notY m
    ref b m
    --deref notX m
    --deref notY m

    res <- disjoin a b m
    ref res m
    --deref a m
    --deref b m

    return res

--Substation array for renaming current state vars to next state
--TODO: no first index
substitutionArray :: [Int] -> [(Int, Int)] -> [Int]
substitutionArray allVars stateVars = map func allVars
    where
    func :: Int -> Int
    func x
        | Just (current, next) <- find (\y -> fst y == x) stateVars = next
        | otherwise                                                 = x

compile :: SDDManager -> [Int] -> [Int] -> [(Int, Int)] -> [(Int, Int, Int)] -> Int -> IO SynthState
compile m controllableInputs uncontrollableInputs latches ands safeIndex = do

    let andGates = map sel1 ands
        andMap   = makeAndMap ands

    bfalse        <- managerFalse m
    btrue         <- managerTrue  m

    --Create the variables
    (cInputVars, endCInputVars, uInputVars, endUInputVars, latchVars, negLatchVars, endLatchVars, latchSddInds :: [(Int, Int)], updateFunctions) 
        <- flip evalStateT 1 $ do

            cInputVars    <- mapM (doLabelVar m) controllableInputs
            endCInputVars <- get

            uInputVars    <- mapM (doLabelVar m) uncontrollableInputs
            endUInputVars <- get

            (latchSddInds, latchVars, negLatchVars, updateFunctions) <- unzip4 <$> mapM (doLatchVar m) latches
            endLatchVars  <- get

            return (concat cInputVars, endCInputVars, concat uInputVars, endUInputVars, concat latchVars, negLatchVars, endLatchVars, latchSddInds, updateFunctions)

    --compute the arrays for quantification
    let allVars    = [0 .. endLatchVars - 1]
        --cInputInds = flip map allVars $ flip elem (map fst cInputVars)
        --uInputInds = flip map allVars $ flip elem (map fst uInputVars)
        cInputInds = flip map allVars (< endCInputVars)
        uInputInds = flip map allVars $ \x -> x >= endCInputVars && x < endUInputVars

    putStrLn $ "cInputVars: " ++ show cInputInds
    putStrLn $ "uInputVars: " ++ show uInputInds
    putStrLn $ "latchVars: "  ++ show latchSddInds

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

    --compile the transition relation
    let func (updateIdx, nextNode) = xnor m nextNode $ fromJustNote "trel lookup" (Map.lookup updateIdx stab)

    putStrLn "Computing xnors"
    trel' <- mapM func updateFunctions

    putStrLn "Computing trel"
    trel  <- computeCube m trel'

    let nextStateInds = flip map allVars $ flip elem (map snd latchSddInds)
        renameMap     = map fromIntegral $ substitutionArray allVars latchSddInds

    print $ "nextStateInds: " ++ show nextStateInds
    print $ "renameMap: "     ++ show renameMap

    --get the safety condition
    let bad   = fromJustNote "compile" $ Map.lookup safeIndex stab
    safe <- neg bad m
    ref safe m
    
    --construct the initial state
    initState <- computeCube m negLatchVars

    return $ SynthState cInputInds uInputInds safe initState renameMap trel nextStateInds

forallMultiple :: [Bool] -> SDDNode -> SDDManager -> IO SDDNode
forallMultiple vars node m = do
    nn    <- neg node m
    ref nn m

    quant <- existsMultiple vars nn m
    ref quant m

    res <- neg quant m
    ref res m
    return res

safeCpre :: SDDManager -> SynthState -> SDDNode -> IO SDDNode
safeCpre m SynthState{..} winning = do
    print "*"

    nextWin <- renameVariables winning renameMap m
    ref nextWin m

    conj <- conjoin trel nextWin m
    ref conj m

    scu' <- existsMultiple nextStateInds conj m 
    ref scu' m

    scu'AndSafe <- conjoin scu' safeRegion m
    ref scu'AndSafe m

    sc <- existsMultiple cInputInds scu'AndSafe m
    ref sc m

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
    ref nx m
    res <- disjoin nx y m
    ref res m
    return res

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

