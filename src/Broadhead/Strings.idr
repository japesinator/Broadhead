module Broadhead.Strings

import Control.Arrow
import Control.Category
import Broadhead.CharSet
import Broadhead.Core
import Broadhead.Combinator
import Broadhead.Prim

char : Char -> BP i Char
char = PEqual

anyChar : BP i Char
anyChar = PCSet CS_Any

wordChar : BP i Char
wordChar = PCSet CS_Word

whiteChar : BP i Char
whiteChar = PCSet CS_Whitespace

digit : BP i Char
digit = PCSet CS_Digit

alnum : BP i Char
alnum = PCSet CS_Alnum

anyOf : Vect n Char -> BP i Char
anyOf = PChoice . (map char)

noneOf : Vect n Char -> BP i Char
noneOf = PNot . anyOf

word :  BP i String
word = some wordChar >>> arrow pack

spaces : BP i String
spaces = some whiteChar >>> arrow pack

string : String -> BP i String
string s with (strM s)
  string ""             | StrNil        = arrow (\_ => "")
  string (strCons x xs) | (StrCons _ _) = arrow  (\_ => ' ')
                                      >>> foldl (>>>)
                                                (char x)
                                                (map char $ unpack xs)
                                      >>> arrow (\_ => (strCons x xs))

Parser : Type -> Type
Parser = BP String

parseString : Parser o -> String -> Either (List String) o
parseString = runParser
