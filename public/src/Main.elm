module Main exposing (..)

import Browser
import Html exposing (..)
import Html.Attributes exposing (..)
import Html.Events exposing (..)
import Parser exposing (..)
import Set
import Dict

main : Program () Model Update
main = Browser.sandbox { 
      init = init
    , view = view
    , update = update
    }

type alias Model = { output : String }

init : Model
init = { output = "" }

type Update = NewCode String

update : Update -> Model -> Model
update msg model = case msg of
    NewCode code -> { model | output = code }

view : Model -> Html Update
view model = div [] 
    [ nav [] 
        [ text "David-Ryan Language" 
        ]
    , div [ id "body" ] 
        [ p [] [ text "Enter code below!" ]
        , textarea 
            [ id "code"
            , placeholder "Write some lambda calculus code! Example: (\\x.\\y.x)(\\x.x)(3)"
            , onInput NewCode 
            ] []
        , br [] []
        , if model.output == "" then text "" else div [] [text "out"]
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

parseNone : Parser Expr
parseNone = keyword "none" |> Parser.map (\_->NoneLit)
parseBool : Parser Expr
parseBool = oneOf [symb "true", symb "false"] |> Parser.map (\s->BoolLit (s == "true"))
parseInt = number {binary=Nothing, float=Nothing, hex=Nothing, int=Just IntLit, octal=Nothing}
parseVar : Parser Expr
parseVar = variable {inner=Char.isAlphaNum, reserved=Set.fromList(["if", "else"]), start=Char.isAlpha}
            |> andThen (\var->
                oneOf 
                    [ succeed (BindLit var)
                        |. ws
                        |. symbol "="
                        |= parse
                        |. symbol ";"
                        |= parse
                    , succeed (VarLit var)
                    ])
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
parseLit = oneOf [parseNone, parseBool, parseInt, parseVar, parseString, parseIf, parenthetical, parseArray]
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
    , symb "+" |> andThen (\c->oneOf 
        [ symb "+"
        , succeed ""
        ] |> andThen (\d->succeed (c++d)))
    , symb "-"
    , symb "*"
    , symb "/"
    , symb "^"
    , symb "%"
    , symb "!="
    , symb "&&"
    ]
parsePrefixOp : Parser String
parsePrefixOp = List.map symb ["!", "-"] |> oneOf
compoundExpr : Expr -> Parser Expr
compoundExpr lit = Parser.loop lit (\left 
            -> succeed identity
            |= oneOf 
                [ parseInfixOp
                    |> andThen (\op-> succeed identity |= parse |> Parser.map (\right->(CallLit (VarLit op) [left, right])))
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
                |> andThen (\op->succeed ((\l->[l])>>CallLit (VarLit op)) |= parseLit)
            , lazy (\_->parseLit)
            ]
          |. ws
          |> andThen compoundExpr

go : String -> Result (List DeadEnd) Expr
go = run (parse|.end)