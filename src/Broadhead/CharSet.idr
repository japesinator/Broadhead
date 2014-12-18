module Broadhead.CharSet

data CharSet = CS_Any
             | CS_Word
             | CS_Whitespace
             | CS_Digit
             | CS_Alpha
             | CS_Alnum
             | CS_Ascii
             | CS_Lower
             | CS_Upper

csetValue : CharSet -> List Char
csetValue CS_Any        = map chr [0..255]
csetValue CS_Word       = ('_' :: csetValue CS_Alnum)
csetValue CS_Whitespace = ['\t','\r','\n']
csetValue CS_Digit      = ['0','1','2','3','4','5','6','7','8','9']
csetValue CS_Ascii      = map chr [0..127]
csetValue CS_Alpha      = filter isAlpha      $ csetValue CS_Any
csetValue CS_Alnum      = csetValue CS_Digit ++ csetValue CS_Alpha
csetValue CS_Lower      = filter isLower      $ csetValue CS_Alpha
csetValue CS_Upper      = filter isUpper      $ csetValue CS_Alpha


instance Show CharSet where
  show CS_Any        = "."
  show CS_Word       = "\\w"
  show CS_Whitespace = "\\s"
  show CS_Digit      = "\\d"
  show CS_Alpha      = "{alpha}"
  show CS_Alnum      = "{alnum}"
  show CS_Ascii      = "{ascii}"
  show CS_Lower      = "{lower}"
  show CS_Upper      = "{upper}"
