﻿module InputLoading
open Yard.Generators.GLL
open Yard.Generators.GLL.ParserCommon
open AbstractAnalysis.Common
open System.Collections.Generic

open Yard.Generators.Common.AutomataCombinators
open Yard.Generators.Common.FSA.Common
open System.IO

(*
ba: ASSERT
ca: ASSERT

s0: C s0 RT s0 | G s0 RL s0 | ca s0 | ca | eps

s1: C s1 RT s1 | G s0 RL s1 | eps

[<Start>]
s: ba s | s ba| s1 s | s s1 | ba | C s RT s1 | C s RT s 
*)

let generateParser calls locks asserts log stage =
    let time = System.DateTime.UtcNow
    stage "Automata construction"
    
    let factory = new AutomataFactory()
    let (~%%), (~&&), (~%), (~&), eps, (=>), (!=>), (<~>), (<|>) = factory.Combinators

    let assertTokens =  [0..asserts - 1] 
                        |> List.map ((sprintf "A%i") >> factory.TerminalToken)

    let callTokens =    [0..calls - 1] 
                        |> List.map ((sprintf "C%i") >> factory.TerminalToken)

    let returnTokens =  [0..calls - 1] 
                        |> List.map ((sprintf "RT%i") >> factory.TerminalToken)

    let getTokens =     [0..locks - 1] 
                        |> List.map ((sprintf "G%i") >> factory.TerminalToken)

    let releaseTokens = [0..locks - 1] 
                        |> List.map ((sprintf "RL%i") >> factory.TerminalToken)

    let asserts = [0..asserts - 1] 
                  |> List.map (fun i -> %assertTokens.[i])
                  |> factory.Alternations
    
    let brackets count (left: EdgeSymbol list) body (right: EdgeSymbol list) =
        List.zip left right
        |> List.map (fun (left, right) -> (%left <~> &body <~> %right))
        |> factory.Alternations
    
    let ba = &&"ba"
    let ca = &&"ca"
    let s0 = &&"s0"
    let s1 = &&"s1"
    let s = &&"s"

    "ba" => asserts
    "ca" => asserts
    "s0" => ((    (brackets calls callTokens s0 returnTokens) 
              <|> (brackets locks getTokens s0 releaseTokens) <~> &s0)
             <|> (&ca <~> (&s0 <|> eps))
             <|> eps)
    "s1" => ((    (brackets calls callTokens s1 returnTokens) 
              <|> (brackets locks getTokens s0 releaseTokens) <~> &s1)
             <|> eps)
    "s" !=> (((brackets calls callTokens s returnTokens) <~> (&s <|> &s1))
             <|> (&s <~> (&s1 <|> &ba))
             <|> (&s1 <~> &s)
             <|> (&ba <~> (&s <|> eps)))

    log (sprintf "Automata construction time is %A" (System.DateTime.UtcNow - time))

    let time = System.DateTime.UtcNow
    stage "Automata conversion"

    let automata = factory.Produce()

    log (sprintf "Automata conversion time is %A" (System.DateTime.UtcNow - time))

    let time = System.DateTime.UtcNow
    stage "Parser generation"

    let gll = new GLL()
    let parser = gll.GenerateFromFSA automata false "gll.fs" :?> ParserSourceGLL

    log (sprintf "Parser generation time is %A" (System.DateTime.UtcNow - time))

    parser

let parseGraphFile (graphStream: TextReader) log stage = 
    let data =    Seq.initInfinite (fun _ -> graphStream.ReadLine()) 
               |> Seq.takeWhile ((<>) null)
               |> Seq.toArray
    
    let data = if data.[data.Length-1].Length < 1 then data.[..data.Length-2] else data
    
    let infoLine = data.[data.Length-2]
    let startVLine = data.[data.Length-1] 
    
    let edgesLines = data.[..data.Length-3]

    let info = infoLine.Split ' '

    let calls = info.[1].Trim() |> int |> fun n -> if (n < 2) then 2 else n
    let locks = info.[2].Trim() |> int |> fun n -> if (n < 2) then 2 else n  
    let asserts = info.[3].Trim() |> int |> fun n -> if (n < 2) then 2 else n

    let parserSource = generateParser calls locks asserts log stage
    let stringToToken = parserSource.StringToToken

    let time = System.DateTime.UtcNow
    stage "Graph loading"

    let tryParseInt str =
        try int str
        with e -> 0

    let startVerts = startVLine.Split ' ' |> Array.map tryParseInt 
    let edges = 
        edgesLines |> Array.map (fun s -> s.Split ' ' |> fun a -> new ParserEdge<_>(int a.[0], int a.[2], stringToToken a.[1]))

    log (sprintf "Graph loading time is %A" (System.DateTime.UtcNow - time))
    
    parserSource, edges, startVerts

let loadInput (graphStream: TextReader) log stage =
    let parserSource, edges, startVerts = parseGraphFile graphStream log stage
    
    let r = new HashSet<_>()
    let ev = edges |> Array.iter (fun e ->
        r.Add e.Source |> ignore
        r.Add e.Target |> ignore)

    log (sprintf "Starts: %A" startVerts.Length)

    let inputGraph = new TokenLabeledInputGraph(startVerts |> Array.filter (fun x -> r.Contains x), [||])
    inputGraph.AddVerticesAndEdgeRange edges |> ignore

    parserSource, inputGraph