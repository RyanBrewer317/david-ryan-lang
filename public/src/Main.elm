module Main exposing (..)

import Browser
import Html exposing (..)
import Html.Attributes exposing (..)
import Html.Events exposing (..)
import Parser exposing (..)
import Set

main : Program () Model Update
main = Browser.sandbox { 
      init = init
    , view = view
    , update = update
    }

type alias Model = { code : String }

init : Model
init = { code = "" }

type Update = NewCode String

update : Update -> Model -> Model
update msg model = case msg of
    NewCode code -> { model | code = code }

view : Model -> Html Update
view model = div [] 
    [ nav [] 
        [ text "David-Ryan Language" 
        ]
    , div [ id "body" ] 
        [ p [] [ text "Enter code below!" ]
        , textarea 
            [ id "code"
            , placeholder "Write some DRL code! Example: ((x)->(y)->x)((x)->x)(3)"
            , onInput NewCode 
            ] []
        , br [] []
        , if model.code == "" then text "" else div [] [text <| Debug.toString <| go model.code]
        , p [] [text "let-binding notation in the above box is ", pre [] [text "a = b; c"], text "where the usual notation is ", pre [] [text "let a = b in c"]]
        ]
    ]

type Expr = NoneLit
          | BoolLit Bool
          | IntLit Int
          | VarLit String
          | StringLit String
          | IfElseLit Expr Expr Expr
          | LambdaLit (List String) Expr
          | CallLit Expr (List Expr)
          | BindLit String Expr Expr
          | TupleLit (List Expr)
          | ArrayLit (List Expr)
          | IndexLit Expr Expr
          | PropLit Expr String

parseNone : Parser Expr
parseNone = keyword "none" |> Parser.map (\_->NoneLit)
parseBool : Parser Expr
parseBool = oneOf [symb "true", symb "false"] |> Parser.map (\s->BoolLit (s == "true"))
parseInt = number {binary=Nothing, float=Nothing, hex=Nothing, int=Just IntLit, octal=Nothing}
parseVar : Parser Expr
parseVar = variable {inner=Char.isAlphaNum, reserved=Set.fromList(["if", "else"]), start=Char.isAlpha}
            |. ws
            |> andThen (\var->
                oneOf 
                    [ succeed (BindLit var)
                        |. symbol "="
                        |= parse
                        |. symbol ";"
                        |= parse
                    , succeed (VarLit var)
                    ])
parseMethodDec = succeed BindLit
              |. symbol "."
              |= (variable {inner=Char.isAlphaNum, reserved=Set.fromList([]), start=Char.isAlpha} |> Parser.map (\s->"."++s))
              |. ws
              |. symbol "="
              |= parse
              |. symbol ";"
              |= parse
parseString : Parser Expr
parseString = succeed StringLit
            |. token "\""
            |= Parser.loop [] (\revChunks->
                oneOf 
                    [ succeed (\chunk -> Loop (chunk::revChunks))
                        |. token "\\"
                        |= oneOf
                            [ Parser.map (\_->"\n") (token "n")
                            , Parser.map (\_->"\t") (token "t")
                            , Parser.map (\_->"\r") (token "r")
                            -- , map (\_->"\"") (token "\"")
                            , chompIf (\_->True) |> getChompedString
                            ]
                    , token "\""
                        |> Parser.map (\_->Done (String.join "" (List.reverse revChunks)))
                    , chompWhile (\c->c/='"'&&c/='\\')
                        |> getChompedString
                        |> Parser.map (\chunk->Loop(chunk::revChunks))
                    ]
            )
parseArray : Parser Expr
parseArray = succeed ArrayLit
        |= sequence
            { start = "["
            , separator = ","
            , end = "]"
            , spaces = ws
            , item = parse
            , trailing = Forbidden
            }
parseIf : Parser Expr
parseIf = succeed IfElseLit
       |. keyword "if"
       |. ws
       |. symbol "("
       |= parse
       |. symbol ")"
       |= parse
       |. keyword "else"
       |= parse
parenthetical : Parser Expr
parenthetical = succeed TupleLit
          |= sequence
            { start = "("
            , item = parse
            , separator = ","
            , end = ")"
            , spaces = ws
            , trailing = Forbidden
            }
          |> Parser.andThen (
            \expr -> 
                case expr of
                    TupleLit xs -> 
                        oneOf 
                            [ succeed identity 
                                |. symbol "->" 
                                |= parse 
                                |> Parser.andThen(\body->
                                    List.foldr (\a b->b|>Maybe.andThen(\bok->
                                        case a of
                                            VarLit n-> Just (n::bok)
                                            _ -> Nothing
                                            )) (Just []) xs
                                            |> Maybe.map (\args->succeed <| LambdaLit args body)
                                            |> Maybe.withDefault (problem "function with non-identifier arguments")
                                    )
                            , succeed (
                                case xs of
                                    [x]->x
                                    _ -> TupleLit xs)
                            ]
                    _ -> succeed expr
          )
parseLit : Parser Expr
parseLit = oneOf [parseNone, parseBool, parseVar, parseMethodDec, parseInt, parseString, parseIf, parenthetical, parseArray]
ws : Parser ()
ws = chompWhile (\c -> c == ' ' || c == '\n' || c == '\r' || c == '\t') |> getChompedString |> Parser.map (\_->())
symb : String -> Parser String
symb s = symbol s |> Parser.map (\_->s)
parseInfixOp : Parser String
parseInfixOp = oneOf 
    [ symb "=" |> andThen (\c->oneOf 
        [ symb ">" 
        , symb "="
        ] |> andThen (\d->succeed (c++d)))
    , symb "<" |> andThen (\c->oneOf
        [ symb "="
        , symb "|"
        , succeed ""
        ] |> andThen (\d->succeed (c++d)))
    , symb ">" |> andThen (\c->oneOf 
        [ symb "="
        , succeed ""
        ] |> andThen (\d->succeed (c++d)))
    , symb "|" |> andThen (\c->oneOf 
        [ symb ">"
        , symb "|"
        ] |> andThen (\d->succeed (c++d)))
    , symb "+" -- the type inferrer should give this the type (a, b)->c and then when the operator is + it should check that the combination of types is valid
    , symb "-"
    , symb "*"
    , symb "/"
    , symb "^"
    , symb "%"
    , symb "!="
    , symb "&&"
    ]
parseProp : Expr -> Parser Expr
parseProp e = succeed (PropLit e) -- the translation of a property to a method needs to happen in type checking, where the type of left is known (ie it may be a struct) and the right is known and/or used (called). If it is a method, the left side needs to be given as the first arg
             |. symbol "."
             |. ws
             |= variable {inner=Char.isAlphaNum, reserved=Set.fromList(["if", "else"]), start=Char.isAlpha}
parsePrefixOp : Parser String
parsePrefixOp = [symb "!", symb "-" |> Parser.map(\_->"--")] |> oneOf -- the -- operator will be understood internally to be the prefix version of the - operator. It should have type a->a, with a hardcoded check that a is an int or float
compoundExpr : Expr -> Parser Expr
compoundExpr lit = Parser.loop lit (\left 
            -> succeed identity
            |= oneOf 
                [ parseInfixOp
                    |> andThen (\op-> succeed identity |= parse |> Parser.map (\right->(CallLit (VarLit op) [left, right])))
                    |> Parser.map Loop
                , parseProp left
                    |> Parser.map Loop
                , sequence
                    { start = "("
                    , item = parse
                    , separator = ","
                    , end = ")"
                    , spaces = ws
                    , trailing = Forbidden
                    }
                    |> Parser.map (CallLit lit >> Loop)
                , succeed (IndexLit lit)
                    |. symbol "["
                    |= parse
                    |. symbol "]"
                    |> Parser.map Loop
                , succeed (Done left)
                ]
            |. ws
    )
parse : Parser Expr
parse = succeed identity
          |. ws
          |= oneOf 
            [ parsePrefixOp
                |> andThen (\op->succeed ((\l->[l])>>CallLit (VarLit op)) |= lazy (\_->parse))
            , lazy (\_->parseLit)
            ]
          |. ws
          |> andThen compoundExpr

go : String -> Result (List DeadEnd) Expr
go = run (parse|.end)