
# 2 "Epsilon.yrd.fs"
module RNGLR.ParseEpsilon
#nowarn "64";; // From fsyacc: turn off warnings that type variables used in production annotations are instantiated to concrete type
open Yard.Generators.RNGLR.Parser
open Yard.Generators.RNGLR
open Yard.Generators.RNGLR.AST
type Token =
    | A of int
    | B of int
    | C of int
    | EOF of int

let numToString = function
    | 0 -> "s"
    | 1 -> "yard_rule_op_1"
    | 2 -> "yard_rule_op_2"
    | 3 -> "yard_rule_op_3"
    | 4 -> "yard_start_rule"
    | 5 -> "A"
    | 6 -> "B"
    | 7 -> "C"
    | 8 -> "EOF"
    | _ -> ""
let tokenToNumber = function
    | A _ -> 5
    | B _ -> 6
    | C _ -> 7
    | EOF _ -> 8

let mutable private cur = 0
let leftSide = [|1; 1; 2; 2; 3; 3; 0; 4|]
let private rules = [|5; 6; 7; 1; 2; 3; 0|]
let private rulesStart = [|0; 0; 1; 1; 2; 2; 3; 6; 7|]
let startRule = 7

let acceptEmptyInput = true

let defaultAstToDot =
    (fun (tree : Yard.Generators.RNGLR.AST.Tree<Token>) -> tree.AstToDot numToString tokenToNumber leftSide)

let private lists_gotos = [|1; 2; 7; 3; 6; 4; 5|]
let private small_gotos =
        [|3; 0; 65537; 327682; 131074; 131075; 393220; 196610; 196613; 458758|]
let gotos = Array.zeroCreate 8
for i = 0 to 7 do
        gotos.[i] <- Array.zeroCreate 9
cur <- 0
while cur < small_gotos.Length do
    let i = small_gotos.[cur] >>> 16
    let length = small_gotos.[cur] &&& 65535
    cur <- cur + 1
    for k = 0 to length-1 do
        let j = small_gotos.[cur + k] >>> 16
        let x = small_gotos.[cur + k] &&& 65535
        gotos.[i].[j] <- lists_gotos.[x]
    cur <- cur + length
let private lists_reduces = [|[|6,1|]; [|6,2|]; [|6,3|]; [|5,1|]; [|3,1|]; [|1,1|]|]
let private small_reduces =
        [|131073; 524288; 196609; 524289; 262145; 524290; 327681; 524291; 393218; 458756; 524292; 458755; 393221; 458757; 524293|]
let reduces = Array.zeroCreate 8
for i = 0 to 7 do
        reduces.[i] <- Array.zeroCreate 9
cur <- 0
while cur < small_reduces.Length do
    let i = small_reduces.[cur] >>> 16
    let length = small_reduces.[cur] &&& 65535
    cur <- cur + 1
    for k = 0 to length-1 do
        let j = small_reduces.[cur + k] >>> 16
        let x = small_reduces.[cur + k] &&& 65535
        reduces.[i].[j] <- lists_reduces.[x]
    cur <- cur + length
let private lists_zeroReduces = [|[|0|]; [|7; 6; 0|]; [|2|]; [|4|]|]
let private small_zeroReduces =
        [|3; 393216; 458752; 524289; 131074; 458754; 524290; 196609; 524291|]
let zeroReduces = Array.zeroCreate 8
for i = 0 to 7 do
        zeroReduces.[i] <- Array.zeroCreate 9
cur <- 0
while cur < small_zeroReduces.Length do
    let i = small_zeroReduces.[cur] >>> 16
    let length = small_zeroReduces.[cur] &&& 65535
    cur <- cur + 1
    for k = 0 to length-1 do
        let j = small_zeroReduces.[cur + k] >>> 16
        let x = small_zeroReduces.[cur + k] &&& 65535
        zeroReduces.[i].[j] <- lists_zeroReduces.[x]
    cur <- cur + length
let private small_acc = [1; 0]
let private accStates = Array.zeroCreate 8
for i = 0 to 7 do
        accStates.[i] <- List.exists ((=) i) small_acc
let eofIndex = 8
let private parserSource = new ParserSource<Token> (gotos, reduces, zeroReduces, accStates, rules, rulesStart, leftSide, startRule, eofIndex, tokenToNumber, acceptEmptyInput)
let buildAst : (seq<Token> -> ParseResult<Token>) =
    buildAst<Token> parserSource

let _rnglr_epsilons : Tree<Token>[] = [|new Tree<_>(null,box (new AST(new Family(6, new Nodes([|box (new AST(new Family(0, new Nodes([||])), null)); box (new AST(new Family(2, new Nodes([||])), null)); box (new AST(new Family(4, new Nodes([||])), null))|])), null)), null); new Tree<_>(null,box (new AST(new Family(0, new Nodes([||])), null)), null); new Tree<_>(null,box (new AST(new Family(2, new Nodes([||])), null)), null); new Tree<_>(null,box (new AST(new Family(4, new Nodes([||])), null)), null); new Tree<_>(null,box (new AST(new Family(7, new Nodes([|box (new AST(new Family(6, new Nodes([|box (new AST(new Family(0, new Nodes([||])), null)); box (new AST(new Family(2, new Nodes([||])), null)); box (new AST(new Family(4, new Nodes([||])), null))|])), null))|])), null)), null)|]
let _rnglr_filtered_epsilons : Tree<Token>[] = [|new Tree<_>(null,box (new AST(new Family(6, new Nodes([|box (new AST(new Family(0, new Nodes([||])), null)); box (new AST(new Family(2, new Nodes([||])), null)); box (new AST(new Family(4, new Nodes([||])), null))|])), null)), null); new Tree<_>(null,box (new AST(new Family(0, new Nodes([||])), null)), null); new Tree<_>(null,box (new AST(new Family(2, new Nodes([||])), null)), null); new Tree<_>(null,box (new AST(new Family(4, new Nodes([||])), null)), null); new Tree<_>(null,box (new AST(new Family(7, new Nodes([|box (new AST(new Family(6, new Nodes([|box (new AST(new Family(0, new Nodes([||])), null)); box (new AST(new Family(2, new Nodes([||])), null)); box (new AST(new Family(4, new Nodes([||])), null))|])), null))|])), null)), null)|]
for x in _rnglr_filtered_epsilons do if x <> null then x.ChooseSingleAst()
let _rnglr_extra_array, _rnglr_rule_, _rnglr_concats = 
  (Array.zeroCreate 0 : array<'_rnglr_type_s * '_rnglr_type_yard_rule_op_1 * '_rnglr_type_yard_rule_op_2 * '_rnglr_type_yard_rule_op_3 * '_rnglr_type_yard_start_rule>), 
  [|
  (
    fun (_rnglr_children : array<_>) (parserRange : (int * int)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            _rnglr_cycle_res := (
              
# 2 "Epsilon.yrd"
                                  1
                )::!_rnglr_cycle_res
            !_rnglr_cycle_res
          )
            )
# 2 "Epsilon.yrd"
               : '_rnglr_type_yard_rule_op_1) 
# 121 "Epsilon.yrd.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (int * int)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with A _rnglr_val -> [_rnglr_val] | a -> failwith "A expected, but %A found" a )
             |> List.iter (fun (_) -> 
              _rnglr_cycle_res := (
                
# 2 "Epsilon.yrd"
                             10
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 2 "Epsilon.yrd"
               : '_rnglr_type_yard_rule_op_1) 
# 141 "Epsilon.yrd.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (int * int)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            _rnglr_cycle_res := (
              
# 2 "Epsilon.yrd"
                                  1
                )::!_rnglr_cycle_res
            !_rnglr_cycle_res
          )
            )
# 2 "Epsilon.yrd"
               : '_rnglr_type_yard_rule_op_2) 
# 159 "Epsilon.yrd.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (int * int)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with B _rnglr_val -> [_rnglr_val] | a -> failwith "B expected, but %A found" a )
             |> List.iter (fun (_) -> 
              _rnglr_cycle_res := (
                
# 2 "Epsilon.yrd"
                             10
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 2 "Epsilon.yrd"
               : '_rnglr_type_yard_rule_op_2) 
# 179 "Epsilon.yrd.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (int * int)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            _rnglr_cycle_res := (
              
# 2 "Epsilon.yrd"
                                  1
                )::!_rnglr_cycle_res
            !_rnglr_cycle_res
          )
            )
# 2 "Epsilon.yrd"
               : '_rnglr_type_yard_rule_op_3) 
# 197 "Epsilon.yrd.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (int * int)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with C _rnglr_val -> [_rnglr_val] | a -> failwith "C expected, but %A found" a )
             |> List.iter (fun (_) -> 
              _rnglr_cycle_res := (
                
# 2 "Epsilon.yrd"
                             10
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 2 "Epsilon.yrd"
               : '_rnglr_type_yard_rule_op_3) 
# 217 "Epsilon.yrd.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (int * int)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_yard_rule_op_1) 
             |> List.iter (fun (a1) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_yard_rule_op_2) 
               |> List.iter (fun (a2) -> 
                ((unbox _rnglr_children.[2]) : '_rnglr_type_yard_rule_op_3) 
                 |> List.iter (fun (a3) -> 
                  _rnglr_cycle_res := (
                    
# 1 "Epsilon.yrd"
                                                           a1 + a2 + a3
                      )::!_rnglr_cycle_res ) ) )
            !_rnglr_cycle_res
          )
            )
# 1 "Epsilon.yrd"
               : '_rnglr_type_s) 
# 241 "Epsilon.yrd.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (int * int)) -> 
      box (
        ( 
          ((unbox _rnglr_children.[0]) : '_rnglr_type_s) 
            )
# 1 "Epsilon.yrd"
               : '_rnglr_type_yard_start_rule) 
# 251 "Epsilon.yrd.fs"
      );
  |] , [|
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_s)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_yard_rule_op_1)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_yard_rule_op_2)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_yard_rule_op_3)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_yard_start_rule)   ) |> List.concat));
  |] 
let translate (args : TranslateArguments<_,_>) (tree : Tree<_>) : '_rnglr_type_yard_start_rule = 
  unbox (tree.Translate _rnglr_rule_  leftSide _rnglr_concats (if args.filterEpsilons then _rnglr_filtered_epsilons else _rnglr_epsilons) args.tokenToRange args.zeroPosition args.clearAST) : '_rnglr_type_yard_start_rule