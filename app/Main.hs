{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE RecordWildCards #-}
module Main where

import           Control.Arrow.Notation
import           Control.Monad
import           Language.Haskell.Exts
import           System.Environment
import           System.Exit
import           Text.Printf

main :: IO ()
main = do
  args <- getArgs
  let exts =
        [
          EnableExtension Arrows
        , EnableExtension DatatypeContexts
        , EnableExtension FlexibleContexts
        , EnableExtension FlexibleInstances
        , EnableExtension FunctionalDependencies
        , EnableExtension GADTs
        , EnableExtension MultiParamTypeClasses
        , EnableExtension MultiWayIf
        , EnableExtension FunctionalDependencies
        , EnableExtension TypeFamilies
        , EnableExtension RecordWildCards
        , EnableExtension ScopedTypeVariables
        , EnableExtension LambdaCase
        ]
  case args of
    [] -> interact $ \inp ->
        case parseModuleWithMode defaultParseMode{extensions=exts} inp of
          ParseOk x ->
            prettyPrint (translateModule $ void x) ++ "\n"
          ParseFailed SrcLoc{..} err ->
            printf "Parse error at %d:%d: %s\n" srcLine srcColumn err
    [orig,inpF,outF] ->
      parseFileWithExts exts inpF >>= \case
        ParseFailed SrcLoc{..} err -> do
          printf "Parse error at %s:%d:%d: %s" orig srcLine srcColumn err
          exitFailure
        ParseOk x -> do
          let x' = translateModule (void x)
          writeFile outF $ prettyPrint x'

    _ -> do
      exe <- getExecutablePath
      putStrLn "Unrecognized arguments. Usage: "
      printf "%s <orig path> <input path> <output path>" exe
