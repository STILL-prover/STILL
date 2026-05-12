module MCP.Server where

import Control.Exception (SomeException, catch, try)
import Control.Monad (unless)
import Data.Map qualified as Map
import MCP.Json
import SessionTypes.Tactics (ProofState (..))
import System.IO
import Parser.CmdParsers (Command (..), TopLevelCommand (..), ProofCommand (..), CommandSpan (spanText, spanValue))
import Utils.Display (renderGoals, renderState)
import Utils.Server (ProcessedScript (..), Snapshot (afterState, beforeState), emptyState, findSnapshotAt, runProofScript, runProofScriptDetailed)
import System.Environment (getExecutablePath)
import System.Directory (doesFileExist)

-- ==========================================
-- Types
-- ==========================================

data JId = JIdInt Int | JIdStr String

data McpRequest = McpRequest
  { reqId :: Maybe JId,
    reqMethod :: String,
    reqParams :: Json
  }

-- ==========================================
-- Response Builders
-- ==========================================

jidToJson :: JId -> Json
jidToJson (JIdInt n) = JNum n
jidToJson (JIdStr s) = JStr s

makeResponse :: JId -> Json -> String
makeResponse jid result =
  renderJson $
    JObj
      [ ("jsonrpc", JStr "2.0"),
        ("id", jidToJson jid),
        ("result", result)
      ]

makeErrorResponse :: JId -> Int -> String -> String
makeErrorResponse jid code msg =
  renderJson $
    JObj
      [ ("jsonrpc", JStr "2.0"),
        ("id", jidToJson jid),
        ("error", JObj [("code", JNum code), ("message", JStr msg)])
      ]

makeToolResult :: JId -> Bool -> String -> String
makeToolResult jid isErr text =
  makeResponse jid $
    JObj
      [ ("content", JArr [JObj [("type", JStr "text"), ("text", JStr text)]]),
        ("isError", JBool isErr)
      ]

makeNullIdError :: Int -> String -> String
makeNullIdError code msg =
  renderJson $
    JObj
      [ ("jsonrpc", JStr "2.0"),
        ("id", JNull),
        ("error", JObj [("code", JNum code), ("message", JStr msg)])
      ]

-- ==========================================
-- Request Parsing
-- ==========================================

parseMcpRequest :: String -> Either String McpRequest
parseMcpRequest line = do
  j <- decodeJson line
  method <- case lookupKey "method" j >>= getString of
    Just m -> Right m
    Nothing -> Left "Missing or non-string 'method' field"
  let rawId = lookupKey "id" j
      jid = case rawId of
        Just (JStr s) -> Just (JIdStr s)
        Just (JNum n) -> Just (JIdInt n)
        _ -> Nothing
      params = case lookupKey "params" j of
        Just v -> v
        Nothing -> JNull
  return McpRequest {reqId = jid, reqMethod = method, reqParams = params}

-- ==========================================
-- Tool Schemas
-- ==========================================

initializeResult :: Json
initializeResult =
  JObj
    [ ("protocolVersion", JStr "2024-11-05"),
      ("capabilities", JObj [("tools", JObj [])]),
      ("serverInfo", JObj [("name", JStr "still"), ("version", JStr "1.0.0")])
    ]

toolsListResult :: Json
toolsListResult = JObj [("tools", JArr [checkProofTool, getProofStateTool, listTheoremsTool, getTacticReferenceTool, getTutorialTool])]

checkProofTool :: Json
checkProofTool =
  JObj
    [ ("name", JStr "check_proof"),
      ("description", JStr "Execute a STILL proof script and return a proof trace showing the goal state after each step, plus any errors. Call get_tactic_reference first to learn available tactics and their semantics before writing proofs."),
      ( "inputSchema",
        JObj
          [ ("type", JStr "object"),
            ("properties", JObj [("text", JObj [("type", JStr "string"), ("description", JStr "The STILL proof script to execute")])]),
            ("required", JArr [JStr "text"])
          ]
      )
    ]

getProofStateTool :: Json
getProofStateTool =
  JObj
    [ ("name", JStr "get_proof_state"),
      ("description", JStr "Get the proof state at a cursor position (0-based line and column) in a STILL proof script."),
      ( "inputSchema",
        JObj
          [ ("type", JStr "object"),
            ( "properties",
              JObj
                [ ("text", JObj [("type", JStr "string"), ("description", JStr "The STILL proof script")]),
                  ("line", JObj [("type", JStr "integer"), ("description", JStr "0-based line number")]),
                  ("col", JObj [("type", JStr "integer"), ("description", JStr "0-based column number")])
                ]
            ),
            ("required", JArr [JStr "text", JStr "line", JStr "col"])
          ]
      )
    ]

listTheoremsTool :: Json
listTheoremsTool =
  JObj
    [ ("name", JStr "list_theorems"),
      ("description", JStr "List all theorems proven in a STILL proof script."),
      ( "inputSchema",
        JObj
          [ ("type", JStr "object"),
            ("properties", JObj [("text", JObj [("type", JStr "string"), ("description", JStr "The STILL proof script")])]),
            ("required", JArr [JStr "text"])
          ]
      )
    ]

getTacticReferenceTool :: Json
getTacticReferenceTool =
  JObj
    [ ("name", JStr "get_tactic_reference"),
      ("description", JStr "Get the complete tactic reference for the STILL prover, including all session type tactics, ECC functional tactics, tacticals, and script-level commands."),
      ("inputSchema", JObj [("type", JStr "object"), ("properties", JObj []), ("required", JArr [])])
    ]

getTutorialTool :: Json
getTutorialTool =
  JObj
    [ ("name", JStr "get_tutorial"),
      ("description", JStr "Get a tutorial for the STILL prover covering proof workflow, worked examples, common patterns, and MCP tool usage."),
      ("inputSchema", JObj [("type", JStr "object"), ("properties", JObj []), ("required", JArr [])])
    ]

-- ==========================================
-- Tool Handlers
-- ==========================================

isProvingCmd :: Command -> Bool
isProvingCmd (TopLevel (CmdTheorem _ _ _)) = True
isProvingCmd (Proof _) = True
isProvingCmd _ = False

stepNewList :: (ProofState -> [String]) -> Snapshot -> [String]
stepNewList field snap =
  let before = length (field (beforeState snap))
      after = field (afterState snap)
  in take (length after - before) after

formatProofStep :: (CommandSpan Command, Snapshot) -> String
formatProofStep (sp, snap) =
  let s = afterState snap
      newErrs = stepNewList errors snap
      errLine = if null newErrs then "" else "\nError: " ++ head newErrs
  in ">> " ++ spanText sp ++ "\n" ++ renderGoals s ++ errLine

handleCheckProof :: JId -> [(String, Json)] -> IO String
handleCheckProof jid args = do
  let text = case lookup "text" args >>= getString of Just t -> t; _ -> ""
  result <- try (runProofScriptDetailed "<mcp>" text) :: IO (Either SomeException (Either String ProcessedScript))
  return $ case result of
    Left ex -> makeToolResult jid True ("Exception: " ++ show ex)
    Right (Left err) -> makeToolResult jid True
        (err ++ "\n\nFor tactic names and descriptions, call get_tactic_reference.")
    Right (Right ps) ->
      let steps = zip (psCommands ps) (psSnaps ps)
          provingSteps = filter (isProvingCmd . spanValue . fst) steps
          traceSection
            | null provingSteps = ""
            | otherwise = "=== Proof Trace ===\n\n"
                ++ concatMap (\step -> formatProofStep step ++ "\n\n") provingSteps
          finalState = case psSnaps ps of [] -> emptyState; snaps -> afterState (last snaps)
          hasErr = not (null (errors finalState))
          body = traceSection
              ++ "Success: " ++ show (not hasErr)
              ++ if hasErr then "\n\nErrors:\n" ++ unlines (reverse (errors finalState)) else ""
       in makeToolResult jid hasErr body

handleGetProofState :: JId -> [(String, Json)] -> IO String
handleGetProofState jid args = do
  let text = case lookup "text" args >>= getString of Just t -> t; _ -> ""
      line0 = case lookup "line" args >>= getInt of Just n -> n; _ -> 0
      col0 = case lookup "col" args >>= getInt of Just n -> n; _ -> 0
      line = line0 + 1
      col = col0 + 1
  result <- try (runProofScriptDetailed "<mcp>" text) :: IO (Either SomeException (Either String ProcessedScript))
  return $ case result of
    Left ex -> makeToolResult jid True ("Exception: " ++ show ex)
    Right (Left err) -> makeToolResult jid True err
    Right (Right ps) ->
      case findSnapshotAt ps line col of
        Nothing -> makeToolResult jid True "No command found at this position."
        Just (_, snap) -> makeToolResult jid False (renderState (afterState snap))

handleListTheorems :: JId -> [(String, Json)] -> IO String
handleListTheorems jid args = do
  let text = case lookup "text" args >>= getString of Just t -> t; _ -> ""
  result <- try (runProofScriptDetailed "<mcp>" text) :: IO (Either SomeException (Either String ProcessedScript))
  return $ case result of
    Left ex -> makeToolResult jid True ("Exception: " ++ show ex)
    Right (Left err) -> makeToolResult jid True err
    Right (Right ps) ->
      let finalState = case psSnaps ps of [] -> emptyState; snaps -> afterState (last snaps)
          names = Map.keys (theorems finalState)
          body = if null names then "No theorems proven." else unlines names
       in makeToolResult jid False body

readDocFile :: String -> IO String
readDocFile filename = do
  exePath <- getExecutablePath
  let exeDir = reverse . dropWhile (\c -> c /= '/' && c /= '\\') . reverse $ exePath
      exePath' = exeDir ++ filename
  exeRelExists <- doesFileExist exePath'
  if exeRelExists
    then readFile exePath'
    else do
      cwdExists <- doesFileExist filename
      if cwdExists
        then readFile filename
        else return ("Documentation file '" ++ filename ++ "' not found. Run 'still serve-mcp' from the STILL project root directory, or see the project repository.")

handleGetTacticReference :: JId -> IO String
handleGetTacticReference jid = do
  result <- try (readDocFile "Tactics.md") :: IO (Either SomeException String)
  return $ case result of
    Left ex -> makeToolResult jid True ("Exception reading Tactics.md: " ++ show ex)
    Right content -> makeToolResult jid False content

handleGetTutorial :: JId -> IO String
handleGetTutorial jid = do
  result <- try (readDocFile "Tutorial.md") :: IO (Either SomeException String)
  return $ case result of
    Left ex -> makeToolResult jid True ("Exception reading Tutorial.md: " ++ show ex)
    Right content -> makeToolResult jid False content

handleToolCall :: JId -> Json -> IO String
handleToolCall jid params =
  case lookupKey "name" params >>= getString of
    Nothing -> return $ makeErrorResponse jid (-32602) "Missing tool name in params"
    Just name ->
      let args = case lookupKey "arguments" params of
            Just (JObj kvs) -> kvs
            _ -> []
       in case name of
            "check_proof" -> handleCheckProof jid args
            "get_proof_state" -> handleGetProofState jid args
            "list_theorems" -> handleListTheorems jid args
            "get_tactic_reference" -> handleGetTacticReference jid
            "get_tutorial" -> handleGetTutorial jid
            _ -> return $ makeErrorResponse jid (-32601) ("Unknown tool: " ++ name)

-- ==========================================
-- Request Dispatch
-- ==========================================

handleRequest :: McpRequest -> IO (Maybe String)
handleRequest req = case reqMethod req of
  "initialize" -> respond initializeResult
  "initialized" -> return Nothing
  "ping" -> respond (JObj [])
  "tools/list" -> respond toolsListResult
  "tools/call" -> case reqId req of
    Nothing -> return Nothing
    Just jid -> Just <$> handleToolCall jid (reqParams req)
  _ -> case reqId req of
    Nothing -> return Nothing
    Just jid -> return . Just $ makeErrorResponse jid (-32601) ("Method not found: " ++ reqMethod req)
  where
    respond result = case reqId req of
      Nothing -> return Nothing
      Just jid -> return . Just $ makeResponse jid result

-- ==========================================
-- Server Loop
-- ==========================================

startMcpServer :: IO ()
startMcpServer = do
  hSetEncoding stdin utf8
  hSetEncoding stdout utf8
  hSetEncoding stderr utf8
  hSetBuffering stdin LineBuffering
  hSetBuffering stdout LineBuffering
  loop
  where
    loop = do
      done <- isEOF
      unless done $ do
        line <- getLine
        case parseMcpRequest (dropWhile (== '\xFEFF') line) of
          Left err -> putStrLn (makeNullIdError (-32700) ("Parse error: " ++ err))
          Right req -> do
            mResp <-
              handleRequest req
                `catch` ( \e -> case reqId req of
                            Nothing -> return Nothing
                            Just jid ->
                              return . Just $
                                makeErrorResponse jid (-32603) (show (e :: SomeException))
                        )
            case mResp of
              Nothing -> return ()
              Just resp -> putStrLn resp
        loop
