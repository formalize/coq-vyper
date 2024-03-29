import Data.List (intercalate)
import System.Environment (getArgs, getProgName)
import System.FilePath (splitExtension)

import Lexer (alexScanTokens)
import Indent (addIndentsAndNewlines)
import Parser (parse)
import PatchedExtracted (compile,
                         l10_decls_to_string, 
                         sample_config, 
                         builtin_names_std,
                         Proto_ast(Build_proto_ast))
import LexerUtils (recognizeKeywords)
import EmbeddedBuiltinsTable (embeddedProtos)

-- Split the command line parameters into options 
-- (starting with '-' but not "-") and arguments.
-- Everything after "--" is considered an argument.
splitArgs :: [String] -> ([String], [String])
splitArgs [] = ([], [])
splitArgs ("--" : rest) = ([], rest)
splitArgs (opt@('-' : h : t) : rest) =
    let (opts, args) = splitArgs rest in (opt : opts, args)
splitArgs (arg : rest) =
    let (opts, args) = splitArgs rest in (opts, arg : args)

compileString :: String -> String
compileString src =
    let l10 = flip parse sample_config $ 
                map snd $ 
                addIndentsAndNewlines $ 
                recognizeKeywords $ 
                alexScanTokens src in
    case compile sample_config builtin_names_std embeddedProtos l10 of
        Left err -> error err
        Right result -> result

compileFileTo :: String -> String -> IO ()
compileFileTo src dst = do
    source <- readFile src
    writeFile dst $ compileString source
      

extIsOk :: String -> Bool
extIsOk ".fe" = True
extIsOk ".vy" = True
extIsOk _ = False

compileFile :: String -> IO ()
compileFile path =
    let (base, ext) = splitExtension path in
    let dst = base ++ ".yul" in
    if extIsOk ext
        then compileFileTo path dst
        else error "Unknown input extension, expected '.fe' or '.vy'"

compileFiles :: [String] -> IO ()
compileFiles = mapM_ compileFile

builtinToString :: Proto_ast -> String
builtinToString (Build_proto_ast name inputs outputs) =
    name ++ "(" ++ intercalate ", " inputs ++ ")" ++
        case outputs of
            [] -> ""
            _ -> " -> " ++ intercalate ", " outputs

dumpBuiltinsHelp = "    --dump-builtins\n\
                   \        Print the table of built-in function prototypes.\n\
                   \        If selected, this must be the only option."
dumpBuiltins :: IO ()
dumpBuiltins = mapM_ putStrLn $ map builtinToString embeddedProtos   

printHelp :: IO ()
printHelp = do
    progName <- getProgName
    putStrLn $ "Usage: " ++ progName ++ " input1.vy input2.vy ..."
    putStrLn "'.fe' extension is accepted as alternative to '.vy'"
    putStrLn ""
    putStrLn "Options:"
    putStrLn dumpBuiltinsHelp

main = do
    (opts, args) <- splitArgs <$> getArgs
    case opts of
        [] -> 
            case args of
                [] -> printHelp
                _ -> compileFiles args
        ["--dump-builtins"] -> dumpBuiltins
        _ -> printHelp
