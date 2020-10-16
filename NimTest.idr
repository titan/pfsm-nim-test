module NimTest

import Data.Maybe
import Data.List
import Data.List1
import Data.SortedMap
import Data.SortedSet
import Data.Strings
import System
import System.File
import System.Random

import Pfsm
import Pfsm.Analyser
import Pfsm.Checker
import Pfsm.Data
import Pfsm.Parser
import Pfsm.Nim

import Stack

Edge : Type
Edge = Transition

Path : Type
Path = List Edge

record AppConfig where
  constructor MkAppConfig
  src : String
  dry : Bool
  dst : String
  refs : List String

indentDelta : Nat
indentDelta = 2

Show AppConfig where
  show (MkAppConfig src model library refs)
    = List.join "\n" [ "src: " ++ src
                     , "model: " ++ (show model)
                     , "library: " ++ (show library)
                     , "refs:"
                     , List.join "\n" $ map (\x => (indent indentDelta) ++ x) refs
                     ]

chars : List Char
chars = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z', ' ']

rndstr : Nat -> IO String
rndstr n
  = rndstr' [] n
  where
    rndstr' : List Char -> Nat -> IO String
    rndstr' acc Z     = pure $ pack acc
    rndstr' acc (S n) = do chr <- rndSelect chars
                           rndstr' (chr :: acc) n

mutual
  rndlist : Nat -> Tipe -> List (IO String)
  rndlist n t
    = rndlist' [] n t
    where
      rndlist' : List (IO String) -> Nat -> Tipe -> List (IO String)
      rndlist' acc Z     t = acc
      rndlist' acc (S n) t = rndlist' ((toNimExample t) :: acc) n t

  rnddict : Nat -> PrimType -> Tipe -> IO (SortedMap String String)
  rnddict n k v
    = rnddict' empty n k v
    where
      rnddict' : SortedMap String String -> Nat -> PrimType -> Tipe -> IO (SortedMap String String)
      rnddict' mappings Z     _ _ = pure mappings
      rnddict' mappings (S n) k v = do k' <- toNimExample (TPrimType k)
                                       v' <- toNimExample v
                                       rnddict' (insert k' v' mappings) n k v

  toNimExample : Tipe -> IO String
  toNimExample (TPrimType PTBool)                    = rndSelect [ "true", "false" ]
  toNimExample (TPrimType PTByte)                    = map (\x => (show x) ++ "'u8") $ randomRIO ((the Int 0), (the Int 255))
  toNimExample (TPrimType PTChar)                    = map (\x => "chr(" ++ (show x) ++ ")") $ liftIO $ randomRIO ((the Int 32), (the Int 127))
  toNimExample (TPrimType PTShort)                   = map (\x => (show x) ++ "'i16") $ randomRIO ((negate $ shiftL 1 15), (shiftL 1 15 - 1))
  toNimExample (TPrimType PTUShort)                  = map (\x => (show x) ++ "'u16") $ randomRIO ((the Int 0), (shiftL 1 16 - 1))
  toNimExample (TPrimType PTInt)                     = map (\x => (show x) ++ "'i32") $ randomRIO ((negate $ shiftL 1 31), (shiftL 1 31 - 1))
  toNimExample (TPrimType PTUInt)                    = map (\x => (show x) ++ "'u32") $ randomRIO ((the Int 0), (shiftL 1 32 - 1))
  toNimExample (TPrimType PTLong)                    = map (\x => (show x) ++ "'i64") $ randomRIO ((negate $ shiftL 1 63), (shiftL 1 63 - 1))
  toNimExample (TPrimType PTULong)                   = map (\x => (show x) ++ "'u64") $ randomRIO ((the Int 0), (shiftL 1 62 - 1))
  toNimExample (TPrimType PTReal)                    = map show $ randomRIO ((the Int 0), (shiftL 1 32 - 1))
  toNimExample (TPrimType PTString)                  = map show $ rndstr 16
  toNimExample (TList t)                             = do strs <- liftListIO $ rndlist 4 t
                                                          pure ("@[ " ++ (List.join ", " strs) ++ " ]")
  toNimExample (TDict PTString (TPrimType PTString)) = do mappings <- rnddict 2 PTString (TPrimType PTString)
                                                          let code = List.join ", " $ map (\(k, v) => k ++ ": " ++ v) $ SortedMap.toList mappings
                                                          pure ("{ " ++ code ++ " }.newStringTable")
  toNimExample (TDict k v)                           = do mappings <- rnddict 2 k v
                                                          let code = List.join ", " $ map (\(k, v) => k ++ ": " ++ v) $ SortedMap.toList mappings
                                                          pure ("{ " ++ code ++ " }.newTable")

  toNimExample (TRecord n ps)                        = do params <- liftListIO $ map (\(n', t, _) => do v <- toNimExample t; pure(n', v)) ps
                                                          pure ((camelize n) ++ "(" ++ (List.join ", " (map (\(n', t) => n' ++ ": " ++ t) params)) ++ ")")

  toNimExample _                                     = pure ""

toNim : AppConfig -> SortedMap Name Fsm -> Fsm -> IO ()
toNim conf refs fsm
  = let name = fsm.name
        pre = camelize (toNimName name)
        start = fromMaybe fsm.states.head $ startState fsm
        stops = filter (start /=) fsm.states
        bpaths = findBasePaths fsm.transitions start stops
        epaths = expandBasePaths fsm.transitions bpaths
        upaths = uniquePaths epaths in
        if conf.dry
           then putStrLn $ join "\n\n" $ map (showPath start) upaths
           else do _ <- liftListIO $ map (generate pre name conf.dst start fsm.model refs) upaths
                   pure ()
  where
    showPath : State -> Path -> String
    showPath start
      = (start.name ++ " " ++ ) . (join " ") . (map showEdge)
      where
        showEdge : Edge -> String
        showEdge (MkTransition src dst ((MkTrigger ((MkParticipant pname _) :: _) (MkEvent ename _ _) _ _) :: _)) = "-(" ++ pname ++ ": " ++ ename ++ ")-> " ++ dst.name
        showEdge (MkTransition src dst _)                                                                         = "-> " ++ dst.name

    findEdgesByDstState : State -> List1 Transition -> List Transition
    findEdgesByDstState s
      = filter (\t => s == t.dst && s /= t.src)

    findBasePath : List1 Edge -> State -> State -> List Path
    findBasePath transitions start stop
      = let ts = findEdgesByDstState stop transitions in
            foldl (\acc, t@(MkTransition src dst _) => if src == start then [t] :: acc else findBasePath' acc [t] transitions (insert src empty) start src) [] ts
      where
        findBasePath' : List Path -> Stack Edge -> List1 Edge -> SortedSet State -> State -> State -> List Path
        findBasePath' acc stack transitions visited start stop
          = let ts = findEdgesByDstState stop transitions in
                foldl (\acc, t@(MkTransition src dst _) => if src == start then (t :: stack) :: acc else if contains src visited then acc else findBasePath' acc (t :: stack) transitions (insert src visited) start src) acc ts

    findBasePaths : List1 Edge -> State -> List State -> List Path
    findBasePaths transitions start stops
      = flatten $ map (findBasePath transitions start) stops

    expandBasePaths : List1 Edge -> List Path -> List Path
    expandBasePaths transitions paths
      = expandBasePaths' [] transitions paths
      where
        expandBasePath : List1 Edge -> Path -> List Path
        expandBasePath transitions path
          = expandBasePath' path transitions path
          where
            findSelfEdge : State -> List1 Edge -> Maybe Edge
            findSelfEdge s ts
              = case filter (\(MkTransition src dst _) => src == s && dst == s) ts of
                     (x :: xs) => Just x
                     [] => Nothing

            expandBasePath' : Path -> List1 Edge -> Path -> List Path
            expandBasePath' orig transitions []                         = [orig]
            expandBasePath' orig transitions [(MkTransition src dst _)] = case (findSelfEdge dst transitions) of
                                                                               Just x => [orig, (orig ++ [x])]
                                                                               Nothing => [orig]
            expandBasePath' orig transitions (x :: xs)                  = expandBasePath' orig transitions xs

        expandBasePaths' : List Path -> List1 Edge -> List Path -> List Path
        expandBasePaths' acc transitions []        = acc
        expandBasePaths' acc transitions (x :: xs) = expandBasePaths' (acc ++ expandBasePath transitions x) transitions xs

    uniquePaths : List Path -> List Path
    uniquePaths paths
      = flatten $ map permutate paths
      where
        splitTrigger : Trigger -> List1 (List1 Trigger)
        splitTrigger (MkTrigger ps e g as)
          = map (\p => (MkTrigger (p :: []) e g as) :: []) $ ps

        splitEdge : Edge -> List1 Edge
        splitEdge e@(MkTransition src dst ts)
          = splitEdge' [] src dst $ List1.flatten $ map splitTrigger ts
          where
            splitEdge' : List Edge -> State -> State -> List1 (List1 Trigger) -> List1 Edge
            splitEdge' acc src dst (x :: [])         = (MkTransition src dst x) :: acc
            splitEdge' acc src dst (x :: (x' :: xs)) = splitEdge' ((MkTransition src dst x) :: acc) src dst (x' :: xs)

        permutate : Path -> List Path
        permutate p
          = let xs = map splitEdge p in
                map reverse $ permutate' [[]] xs
          where
            permutate' : List (Stack Edge) -> List (List1 Edge) -> List (Stack Edge)
            permutate' parents []            = parents
            permutate' parents (es :: edges) = let es' = List1.toList es
                                                   newparents = flatten $ map (\parent => map (\x => push x parent) es') parents in
                                                   permutate' newparents edges

    liftReference : Fsm -> Maybe (Name, Event, List1 Participant)
    liftReference fsm@(MkFsm name _ _ events _ transitions _)
      = let evts = foldl (\acc, evt@(MkEvent _ _ ms) =>
                     case lookup "creator" ms of
                          Just _ => evt :: acc
                          Nothing => acc) (the (List Event) []) events
            xs = foldl (\acc, evt =>
                   foldl (\acc', (MkTransition _ _ ts) =>
                     foldl (\acc'', (MkTrigger ps e _ _) =>
                       if e == evt
                          then (name, e, ps) :: acc''
                          else acc'') acc' ts) acc transitions) [] evts in
            if List.length xs > 0
               then head' xs
               else Nothing

    generatePreface : String
    generatePreface
      = List.join "\n" [ "discard \"\"\""
                       , (indent indentDelta) ++ "output: \'\'\'"
                       , "Success"
                       , "\'\'\'"
                       , "\"\"\""
                       ]

    generateImports : List String -> String
    generateImports services
      = join "\n" $ List.filter nonblank [ "import db_mysql, md5, net, options, os, osproc, std/sha1, strtabs, strutils, tables, test_helper, times"
                                         , "import redis except `%`"
                                         , List.join "\n" $ map (("import " ++) . toNimName) services
                                         ]

    generateSetup : List String -> List Participant -> String
    generateSetup services participants
      = List.join "\n" [ "proc setup(): void ="
                       , (indent indentDelta) ++ "let"
                       , (indent (indentDelta * 2)) ++ "sqlstmt = sql\"SELECT CONCAT('drop table ',table_name,';') FROM information_schema.`TABLES` WHERE table_schema=?\""
                       , (indent (indentDelta * 2)) ++ "dbconn = open(\"%%DBSERVER%%\", \"%%DBUSER%%\", \"%%DBPASSWD%%\", \"%%DBNAME%%\")"
                       , (indent (indentDelta * 2)) ++ "rows = dbconn.getAllRows(sqlstmt, \"%%DBNAME%%\")"
                       , (indent (indentDelta * 2)) ++ "cache = open(\"%%CACHE-HOST%%\", %%CACHE-PORT%%.Port)"
                       , (indent indentDelta) ++ "for row in rows:"
                       , (indent (indentDelta * 2)) ++ "discard dbconn.tryExec(sql(row[0]))"
                       , (indent indentDelta) ++ "close(dbconn)"
                       , (indent indentDelta) ++ "discard cache.select(1)"
                       , (indent indentDelta) ++ "discard cache.flushdb()"
                       , (indent indentDelta) ++ "discard quit(cache)"
                       , List.join "\n" $ map (\(i, x) => generateStartGetway indentDelta i x) $ enumerate participants
                       , List.join "\n" $ map (generateStartService indentDelta) services
                       , (indent indentDelta) ++ "sleep(1000)"
                       ]
      where
        generateStartGetway : Nat -> Nat -> Participant -> String
        generateStartGetway idt idx (MkParticipant name _)
          = (indent idt) ++ "processes &= startProcess(\"" ++ (name ++ "-server") ++ "\", args = [\"--redis-db=1\", \"--port=808" ++ (show idx) ++ "\", \"1\"])"

        generateStartService : Nat -> String -> String
        generateStartService idt name
          = (indent idt) ++ "processes &= startProcess(\"" ++ (name) ++ "\", args = [\"--redis-db=1\"])"

    generateTeardown : String
    generateTeardown
      = List.join "\n" [ "proc teardown(): void ="
                       , (indent indentDelta) ++ "for p in processes:"
                       , (indent (indentDelta * 2)) ++ "kill(p)"
                       , (indent (indentDelta * 2)) ++ "close(p)"
                       ]

    generateTest : String -> String -> State -> List Participant -> List (Name, Event, List1 Participant) -> Path -> IO String
    generateTest pre name start participants refers path
      = do codes <- liftListIO $ map (generateStep indentDelta name start) path
           referCodes <- liftListIO $ map (generateInitReference indentDelta) $ reverse refers
           pure $ List.join "\n" [ "proc test(): void ="
                                 , (indent indentDelta) ++ "let"
                                 , (indent (indentDelta * 2)) ++ "expireat = fromUnix(now().toTime.toUnix + 365 * 24 * 60 * 60).utc.format(\"yyMMddHHmmssffffff\").parseBiggestUInt"
                                 , List.join "\n" $ map (\(i, x) => generateInitParticipant (indentDelta * 2) i x) $ enumerate participants
                                 , List.join "\n" referCodes
                                 , (indent indentDelta) ++ "var"
                                 , (indent (indentDelta * 2)) ++ "found = false"
                                 , (indent (indentDelta * 2)) ++ "objs: seq[" ++ pre ++ "] = @[]"
                                 , List.join "\n" codes
                                 , (indent indentDelta) ++ "echo \"Success\""
                                 ]
      where
        liftCreatorParameters : List Parameter -> IO (List String)
        liftCreatorParameters params
          = liftListIO $ map (\(_, t, metas) =>
                           case lookup "reference" metas of
                                Just (MVString ref) => pure ((toNimName ref) ++ "_id")
                                _ => toNimExample t) params

        generateInitReference : Nat -> (Name, Event, List1 Participant) -> IO String
        generateInitReference idt (ref, (MkEvent ename params ms), ((MkParticipant pname _) :: _))
          = do params <- liftCreatorParameters params
               let code = List.join "\n" [ (indent idt) ++ "let " ++ (toNimName ref) ++ "_id_opt = " ++ (toNimName ref) ++ "." ++ (toNimFuncName ename) ++ "(" ++ (toNimName pname) ++ "_caller, " ++ (List.join ", " params) ++ ")"
                                         , (indent idt) ++ "if " ++ (toNimName ref) ++ "_id_opt.isNone:"
                                         , (indent (idt + indentDelta)) ++ "echo \"Failure in reference " ++ ref ++ "\""
                                         , (indent (idt + indentDelta)) ++ "return"
                                         , (indent idt) ++ "let " ++ (toNimName ref) ++ "_id = " ++ (toNimName ref) ++ "_id_opt.get"
                                         ]
               pure code

        generateInitParticipant : Nat -> Nat -> Participant -> String
        generateInitParticipant idt idx (MkParticipant pname _)
          = List.join "\n" [ (indent idt) ++ (toNimName pname) ++ "_caller = Caller("
                           , (indent (idt + indentDelta)) ++ "host: \"127.0.0.1\","
                           , (indent (idt + indentDelta)) ++ "port: 808" ++ (show idx) ++ ","
                           , (indent (idt + indentDelta)) ++ "tenant: 1'u64,"
                           , (indent (idt + indentDelta)) ++ "appid: getMD5(\"1\"),"
                           , (indent (idt + indentDelta)) ++ "appkey: $secureHash(\"1\" & \"" ++ pname ++ "\") & $secureHash(getMD5(\"1\") & \"" ++ pname ++ "\"),"
                           , (indent (idt + indentDelta)) ++ "access_token: toHex(" ++ (show idx) ++ "'u64 + expireat) & toHex(" ++ (show idx) ++ "'u64 - expireat),"
                           , (indent (idt + indentDelta)) ++ "refresh_token: \"\","
                           , (indent idt) ++ ")"
                           ]

        generateEventCall : Nat -> Name -> Bool -> List String -> Participant -> Event -> Maybe TestExpression -> String
        generateEventCall idt name True  params (MkParticipant pname _) (MkEvent ename _ _) guard
          = let params' = join ", " params in
                List.join "\n" [ (indent idt) ++ "let fsmid_opt = " ++ (toNimName name) ++ "." ++ (toNimName ename) ++ "(" ++ (toNimName pname) ++ "_caller, " ++ params' ++ ")"
                               , (indent idt) ++ "if fsmid_opt.isNone:"
                               , (indent (idt + indentDelta)) ++ "echo \"Failure in event " ++ ename ++ "\""
                               , (indent (idt + indentDelta)) ++ "return"
                               , (indent idt) ++ "let fsmid = fsmid_opt.get"
                               ]

        generateEventCall idt name False params (MkParticipant pname _) (MkEvent ename _ _) guard
          = let params' = join ", " params in
                (indent idt) ++ "discard " ++ (toNimName name) ++ "." ++ (toNimName ename) ++ (if (length params') > Z then "(" ++ (toNimName pname) ++ "_caller, fsmid, " ++ params' ++ ")" else ("(" ++ (toNimName pname) ++ "_caller, fsmid)"))

        generateStateFetch : Nat -> Name -> Participant -> State -> String
        generateStateFetch idt name (MkParticipant pname _) (MkState sname _ _ _)
          = List.join "\n" [ (indent idt) ++ "objs = " ++ (toNimName pname) ++ "_caller.get_" ++ (toNimName sname) ++ "_" ++ (toNimName name) ++ "_list(0, 0x7FFFFFFF)"
                           , (indent idt) ++ "found = false"
                           , (indent idt) ++ "for obj in objs:"
                           , (indent (idt + indentDelta)) ++ "if obj.fsmid == fsmid:"
                           , (indent (idt + indentDelta * 2)) ++ "found = true"
                           , (indent (idt + indentDelta * 2)) ++ "break"
                           , (indent idt) ++ "if not found:"
                           , (indent (idt + indentDelta)) ++ "echo \"Failure in state " ++ sname ++ "\""
                           , (indent (idt + indentDelta)) ++ "return"
                           ]

        generateStep : Nat -> String -> State -> Edge -> IO String
        generateStep idt name start (MkTransition src dst ((MkTrigger (participant :: _) evt@(MkEvent _ params _) guard _) :: _))
          = do params' <- liftCreatorParameters params
               pure $ List.join "\n" [ generateEventCall idt name (src == start) params' participant evt guard
                                     , generateStateFetch idt name participant dst
                                     ]

    generateMain : String
    generateMain
      = List.join "\n" [ "proc main() ="
                       , (indent indentDelta) ++ "setup()"
                       , (indent indentDelta) ++ "try:"
                       , (indent (indentDelta * 2)) ++ "test()"
                       , (indent indentDelta) ++ "except:"
                       , (indent (indentDelta * 2)) ++ "discard"
                       , (indent indentDelta) ++ "teardown()"
                       ]

    generateBoot : String
    generateBoot
      = List.join "\n" [ "when isMainModule:"
                       , (indent indentDelta) ++ "main()"
                       ]

    generate : String -> String -> String -> State -> List Parameter -> SortedMap Name Fsm -> Path -> IO ()
    generate pre name dstpath start model refs path
      = let filename = dstpath ++ "/" ++ (pathToFilename start path) ++ ".nim"
            participants = nub $ map (\(MkTransition _ _ ((MkTrigger (p :: _) _ _ _):: _)) => p) path

            refers = nubBy (\(n1, e1, ps1), (n2, e2, ps2) => n1 == n2 && e1 == e2 && (List1.toList ps1) == (List1.toList ps2)) $ fromMaybe (the (List (Name, Event, List1 Participant)) []) $ liftMaybeList $ map liftReference $ values refs
            referParticipants = flatten $ map (\(_, _, ps) => List1.toList ps) refers
            participants' = nub (participants ++ referParticipants)
            services = nub (name :: (map (\(n, _, _) => n) refers))
            preface = generatePreface
            imports = generateImports services
            setup = generateSetup services participants'
            teardown = generateTeardown
            main = generateMain
            boot = generateBoot in
            do test <- generateTest pre name start participants' refers path
               let code = List.join "\n\n" [ preface
                                           , imports
                                           , "var processes: seq[Process] = @[]"
                                           , setup
                                           , teardown
                                           , test
                                           , main
                                           , boot
                                           ]
               Right _ <- writeFile filename code
               | Left err => putStrLn $ show err
               pure ()
      where
        edgeToFilename : Edge -> String
        edgeToFilename (MkTransition _ (MkState sname _ _ _) ((MkTrigger ((MkParticipant pname _) :: _) (MkEvent ename _ _) _ _) :: _)) = (toNimName pname) ++ "_" ++ (toNimName ename) ++ "_" ++ (toNimName sname)
        edgeToFilename (MkTransition _ (MkState sname _ _ _) _)                                                                         = (toNimName sname)

        pathToFilename : State -> Path -> String
        pathToFilename (MkState sname _ _ _) path
          = "test_" ++ (toNimName sname) ++ "_" ++ (join "_" (map edgeToFilename path))

doWork : AppConfig -> IO ()
doWork conf
  = do refs <- liftListIO $ map loadFsmFromFile conf.refs
       let (errs, fsms) = liftEitherList refs
       if length errs > 0
          then putStrLn $ List.join "\n" errs
          else case checkReferences fsms of
                    Left err => putStrLn err
                    Right mappings => do Right fsm <- loadFsmFromFile conf.src
                                         | Left err => putStrLn err
                                         let (errs', _) = liftEitherList $ map (checkReference mappings) $ liftReferences fsm
                                         if length errs' > 0
                                            then putStrLn $ List.join "\n" errs'
                                            else toNim conf mappings fsm
  where
    liftReferences : Fsm -> List String
    liftReferences fsm
      = foldl (\acc, (_, _, ms) =>
                case lookup "reference" ms of
                     Just (MVString ref) => ref :: acc
                     _ => acc) [] fsm.model

    checkReference : SortedMap Name Fsm -> Name -> Either String Name
    checkReference mappings ref
      = case lookup ref mappings of
             Just _ => Right ref
             Nothing => Left ("Missing reference of " ++ ref)

    checkReferences : List Fsm -> Either String (SortedMap Name Fsm)
    checkReferences fsms
      = let mappings = foldl (\acc, x => insert x.name x acc) empty fsms
            refs = flatten $ map liftReferences fsms
            (errs, _) = liftEitherList $ map (checkReference mappings) refs in
            if length errs > 0
               then Left $ List.join "\n" errs
               else Right mappings

parseArgs : List String -> Maybe AppConfig
parseArgs
  = parseArgs' Nothing False Nothing []
  where
    parseArgs' : Maybe String -> Bool -> Maybe String -> List String -> List String -> Maybe AppConfig
    parseArgs' Nothing    _     _          refs []                = Nothing
    parseArgs' (Just src) True  _          refs []                = Just (MkAppConfig src True "" refs)
    parseArgs' (Just src) False (Just dst) refs []                = Just (MkAppConfig src False dst refs)
    parseArgs' src        _     dst        refs ("--dry" :: xs)   = parseArgs' src True dst refs xs
    parseArgs' src        dry   _          refs ("-d" :: x :: xs) = parseArgs' src dry (Just x) refs xs
    parseArgs' src        dry   dst        refs ("-r" :: x :: xs) = parseArgs' src dry dst (x :: refs) xs
    parseArgs' _          dry   dst        refs (x :: xs)         = parseArgs' (Just x) dry dst refs xs
    parseArgs' _          _     _          _    _                 = Nothing

usage : String
usage
  = List.join "\n" [ "Usage: pfsm-to-nim-test [options] <src>"
                   , ""
                   , "Options:"
                   , "  --dry        Don't generate test suites. Just print test path [default: false]."
                   , "  -d <path>    The destination path to save generated test suites."
                   , "  -r <path>    The path of referenced fsm defination."
                   ]

main : IO ()
main
  = do args <- getArgs
       case tail' args of
            Nothing => putStrLn usage
            Just args' => case parseArgs args' of
                               Just conf => doWork conf
                               Nothing => putStrLn usage
