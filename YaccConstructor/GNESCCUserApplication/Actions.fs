//this file was generated by GNESCC
//source grammar:D:\YC\recursive-ascent\Tests\GNESCC\test_seq\test_seq.yrd
//date:10/8/2011 6:41:54 PM

module GNESCC.Actions

open Yard.Generators.GNESCCGenerator

let getUnmatched x expectedType =
    "Unexpected type of node\nType " + x.ToString() + " is not expected in this position\n" + expectedType + " was expected." |> failwith

let value x = (x:>Lexer_seq.MyLexeme).MValue

let s0 expr = 
    let inner  = 
        match expr with
        | RESeq [gnescc_x0] -> 
            let (gnescc_x0) =
                let yardElemAction expr = 
                    match expr with
                    | REClosure(lst) -> 
                        let yardClsAction expr = 
                            match expr with
                            | RESeq [gnescc_x0; gnescc_x1] -> 
                                let (gnescc_x0) =
                                    let yardElemAction expr = 
                                        match expr with
                                        | RELeaf tPLUS -> tPLUS :?> 'a
                                        | x -> getUnmatched x "RELeaf"

                                    yardElemAction(gnescc_x0)
                                let (gnescc_x1) =
                                    let yardElemAction expr = 
                                        match expr with
                                        | RELeaf s -> (s :?> _ ) 
                                        | x -> getUnmatched x "RELeaf"

                                    yardElemAction(gnescc_x1)
                                (gnescc_x0,gnescc_x1 )
                            | x -> getUnmatched x "RESeq"

                        List.map yardClsAction lst 
                    | x -> getUnmatched x "REClosure"

                yardElemAction(gnescc_x0)
            (gnescc_x0 )
        | x -> getUnmatched x "RESeq"
    box (inner)

let ruleToAction = dict [|(1,s0)|]
