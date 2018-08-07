namespace LockChecker

open Yard.Generators.GLL
open Yard.Generators.GLL.ParserCommon
open Yard.Generators.Common.AutomataCombinators
open Yard.Generators.Common.FSA.Common
open AbstractAnalysis.Common

open AbstractParser

module Parsing =
    let generateParser calls locks asserts =
        let time = System.DateTime.UtcNow
        Logging.stage "Automata construction"
        
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
    
        Logging.log (sprintf "Automata construction time is %A" (System.DateTime.UtcNow - time))
    
        let time = System.DateTime.UtcNow
        Logging.stage "Automata conversion"

        let automata = factory.Produce()

        Logging.log (sprintf "Automata conversion time is %A" (System.DateTime.UtcNow - time))

        let time = System.DateTime.UtcNow
        Logging.stage "Parser generation"

        let gll = new GLL()
        let parser = gll.GenerateFromFSA automata false "gll.fs" :?> ParserSourceGLL

        Logging.log (sprintf "Parser generation time is %A" (System.DateTime.UtcNow - time))

        parser
    
    let parseGraph parserSource inputGraph =
        getAllSPPFRootsAsINodes parserSource inputGraph
