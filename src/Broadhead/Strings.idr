module Broadhead.Strings

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

word :  BP i String
word = some wordChar >>> arrow pack

spaces : BP i String
spaces = some whiteChar >>> arrow pack

string : String -> BP i String
string "" = arrow (\_ => "")
string s  = arrow (\_ => ' ')
        >>> foldr (>>>) (char $ strHead s) (map char (unpack $ strTail s))
        >>> arrow (\_ => s)

Parser : Type -> Type
Parser = BP String

parseString : Parser o -> String -> Either (List String) o
parseString = runParser
