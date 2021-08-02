import System.Environment (getArgs, getProgName)
import Data.List (intercalate)

import Lexer (alexScanTokens)
import Indent (addIndentsAndNewlines)
import BuiltinsParser (parse)
import PatchedExtracted (Proto_ast(Build_proto_ast))

toStringLiteral name = "\"" ++ name ++ "\""

toString [] = "[]"

toCommaSeparatedList types = intercalate ", " $ map toStringLiteral types
toListLiteral types = "[" ++ toCommaSeparatedList types ++ "]"

translateProto :: Proto_ast -> String
translateProto (Build_proto_ast name inputTypes outputTypes) =
    "    Build_proto_ast " ++ toStringLiteral name ++ " " ++ 
                          toListLiteral inputTypes ++ " " ++
                          toListLiteral outputTypes

modIntro = "module EmbeddedBuiltinsTable where\n"
imports = "import PatchedExtracted (Proto_ast(Build_proto_ast))\n"

translate :: String -> String -> String
translate banner src =
    let protos = parse $ map snd $ addIndentsAndNewlines $ alexScanTokens src in
        banner ++ modIntro ++ "\n" ++ imports ++ 
            "\n\nembeddedProtos = [\n" ++
            intercalate ",\n" (map translateProto protos) ++
            "]"

translateFile banner srcPath dstPath = do
    src <- readFile srcPath
    writeFile dstPath $ translate banner src

printHelp = do
    progName <- getProgName
    putStrLn $ progName ++ " - read a list of builtins and generate a Haskell source with the AST"
    putStrLn $ "Usage: " ++ progName ++ "input.list output.hs"

makeBanner = do
    progName <- getProgName
    args <- getArgs
    pure $ "-- This file was generated by " ++ progName ++ " with the following args: " ++ unwords args ++ "\n"

main = do
    args <- getArgs
    banner <- makeBanner
    case args of 
        [srcPath, dstPath] -> translateFile banner srcPath dstPath
        _ -> printHelp
