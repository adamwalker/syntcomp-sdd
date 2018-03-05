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
        deref accum m
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
    updateMap     :: [(Int, SDDNode)]
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
    --liftIO $ ref sddNode m

    negated <- liftIO $ neg sddNode m
    --liftIO $ ref negated m

    return $ [(idx, sddNode), (idx + 1, negated)]

doLatchVar :: SDDManager -> (Int, Int) -> StateT Int IO ((Int, Int), [(Int, SDDNode)], SDDNode, (Int, Int, SDDNode))
doLatchVar m (idx, updateFunc) = do
    --Reserve indices
    currentIdx <- reserveSDDVar
    nextIdx    <- reserveSDDVar

    --Create the SDD nodes for the indices
    sddNode     <- liftIO $ managerLiteral (fromIntegral currentIdx) m
    --liftIO $ ref sddNode m

    sddNodeNext <- liftIO $ managerLiteral (fromIntegral nextIdx)    m
    --liftIO $ ref sddNodeNext m

    --For the symbol table
    negated <- liftIO $ neg sddNode m
    --liftIO $ ref negated m
    let stab = [(idx, sddNode), (idx + 1, negated)]

    --The update function
    let update = (updateFunc, nextIdx, sddNodeNext)

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
    deref notX m
    deref notY m

    res <- disjoin a b m
    ref res m
    deref a m
    deref b m

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

    --putStrLn $ "cInputVars: " ++ show cInputInds
    --putStrLn $ "uInputVars: " ++ show uInputInds
    --putStrLn $ "latchVars: "  ++ show latchSddInds

    --putStrLn $ "endLatchVars: " ++ show endLatchVars

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

    --compile the transition relation
    let func (updateIdx, nextIdx, nextNode) = do
            trel <- xnor m nextNode $ fromJustNote "trel lookup" (Map.lookup updateIdx stab)
            return (nextIdx, trel)

    --putStrLn "Computing xnors"
    updateMap <- mapM func updateFunctions

    let renameMap = map fromIntegral $ substitutionArray allVars latchSddInds

    --print $ "renameMap: " ++ show renameMap

    --get the safety condition
    let bad   = fromJustNote "compile" $ Map.lookup safeIndex stab
    safe <- neg bad m
    ref safe m
    
    --construct the initial state
    initState <- computeCube m negLatchVars

    return $ SynthState cInputInds uInputInds safe initState renameMap updateMap

forallMultiple :: [Bool] -> SDDNode -> SDDManager -> IO SDDNode
forallMultiple vars node m = do
    nn    <- neg node m
    ref nn m

    quant <- existsMultiple vars nn m
    ref quant m
    deref nn m

    res <- neg quant m
    ref res m
    deref quant m
    return res

doTrel :: SDDManager -> [(Int, SDDNode)] -> SDDNode -> IO (SDDNode)
doTrel m updateMap nextWin = foldM func nextWin updateMap
    where
    func :: SDDNode -> (Int, SDDNode) -> IO SDDNode
    func accum (nextIdx, update) = do
        conj <- conjoin accum update m
        ref conj m
        deref accum m

        res <- exists (fromIntegral nextIdx) conj m
        ref res m
        deref conj m

        return res

safeCpre :: SDDManager -> SynthState -> SDDNode -> IO SDDNode
safeCpre m SynthState{..} winning = do
    print "*"

    --putStrLn "rename"
    nextWin <- renameVariables winning renameMap m
    ref nextWin m

    --putStrLn "exists next"
    scu' <- doTrel m updateMap nextWin
    ref scu' m

    --putStrLn "conjoin safe"
    scu'AndSafe <- conjoin scu' safeRegion m
    ref scu'AndSafe m
    deref scu' m

    --putStrLn "exists input"
    sc <- existsMultiple cInputInds scu'AndSafe m
    ref sc m
    deref scu'AndSafe m

    --putStrLn "forall uncontrollable"
    s <- forallMultiple uInputInds sc m
    deref sc m

    --putStrLn "done"
    return s

fixedPoint :: SDDManager -> SDDNode -> (SDDNode -> IO SDDNode) -> IO SDDNode
fixedPoint m start func = do

    --putStrLn "collecting garbage"
    --garbageCollect m
    --putStrLn "reordering"
    --minimize m
    --putStrLn "done"

    res <- func start
    deref start m

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

        m <- managerCreate (fromIntegral (i + 2*l + 1)) 1

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

