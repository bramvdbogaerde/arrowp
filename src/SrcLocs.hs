{-# LANGUAGE DeriveDataTypeable #-}
module SrcLocs where

import           Data.Data
import           Data.Default
import           Language.Haskell.Exts

-- | The type of src code locations used by arrowp-qq
newtype S = S {getSrcSpanInfo :: SrcSpanInfo}
  deriving (Eq, Ord, Data, Typeable)
instance Show S where show _ = "<loc>"

instance Default S where
  def = S noSrcSpan

