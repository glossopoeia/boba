module Lexer
# 1 ".\Lexer.fsl"
 
open FSharp.Text.Lexing
open System
open Parser
open Boba.Compiler.Syntax
open Boba.Core.Types

let lexeme lexbuf = LexBuffer<_>.LexemeString lexbuf

# 12 "Lexer.fs"
let trans : uint16[] array = 
    [| 
    (* State 0 *)
     [| 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 1us; 2us; 65535us; 65535us; 3us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 1us; 65535us; 5us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 4us; 4us; 4us; 4us; 4us; 4us; 4us; 4us; 4us; 4us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; |];
    (* State 1 *)
     [| 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; |];
    (* State 2 *)
     [| 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; |];
    (* State 3 *)
     [| 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 2us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; |];
    (* State 4 *)
     [| 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 8us; 8us; 8us; 8us; 8us; 8us; 8us; 8us; 8us; 8us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; |];
    (* State 5 *)
     [| 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 6us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 65535us; |];
    (* State 6 *)
     [| 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 6us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 65535us; |];
    (* State 7 *)
     [| 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 6us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 7us; 65535us; |];
    (* State 8 *)
     [| 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 8us; 8us; 8us; 8us; 8us; 8us; 8us; 8us; 8us; 8us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; |];
    |] 
let actions : uint16[] = [|65535us; 0us; 1us; 65535us; 2us; 65535us; 3us; 65535us; 2us; |]
let _fslex_tables = FSharp.Text.Lexing.UnicodeTables.Create(trans,actions)
let rec _fslex_dummy () = _fslex_dummy() 
// Rule token
and token  lexbuf =
  match _fslex_tables.Interpret(0,lexbuf) with
  | 0 -> ( 
# 16 ".\Lexer.fsl"
                               token lexbuf 
# 43 "Lexer.fs"
          )
  | 1 -> ( 
# 17 ".\Lexer.fsl"
                             token lexbuf 
# 48 "Lexer.fs"
          )
  | 2 -> ( 
# 18 ".\Lexer.fsl"
                            INTEGER ({ Value = lexeme lexbuf; Size = ISize; Position = lexbuf.StartPos }) 
# 53 "Lexer.fs"
          )
  | 3 -> ( 
# 19 ".\Lexer.fsl"
                                     STRING ({ Value = lexeme lexbuf; Position = lexbuf.StartPos }) 
# 58 "Lexer.fs"
          )
  | _ -> failwith "token"

# 3000000 "Lexer.fs"
