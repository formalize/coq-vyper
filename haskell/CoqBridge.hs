module CoqBridge where

import Data.Bits
import PatchedExtracted

posOfInteger :: Integer -> Positive
posOfInteger 1 = XH
posOfInteger x | x > 0 =
    (if x .&. 1 /= 0 then XI else XO) $ posOfInteger $ x `shiftR` 1

zOfInteger :: Integer -> Z
zOfInteger 0 = Z0
zOfInteger x | x > 0 = Zpos $ posOfInteger x
zOfInteger x = Zneg $ posOfInteger $ -x
