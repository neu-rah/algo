{-# LANGUAGE OverloadedStrings #-}
module AlgParser where

import AlgData
import Data.String

instance Read Algo
instance IsString Algo
