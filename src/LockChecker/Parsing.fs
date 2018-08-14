namespace LockChecker

open Yard.Generators.GLL
open Yard.Generators.GLL.ParserCommon
open Yard.Generators.Common.AutomataCombinators
open Yard.Generators.Common.FSA.Common
open AbstractAnalysis.Common
open QuickGraph

open AbstractParser

type TokenLabeledInputGraph(initialVertices : int[], finalVertices : int[]) =
    inherit AdjacencyGraph<int, ParserEdge<int<token>>>()

    interface IParserInput with
        member this.InitialPositions = 
            Array.map(fun x -> x * 1<positionInInput>) initialVertices
        
        member this.FinalPositions = 
            Array.map(fun x -> x * 1<positionInInput>) finalVertices

        member this.ForAllOutgoingEdges curPosInInput pFun =
            let rec forAllOutgoingEdgesAndEpsilons start =
                let edges = start |> this.OutEdges
                edges |> Seq.iter
                    (
                        fun e -> 
                            if e.Tag = -1<token> then
                                forAllOutgoingEdgesAndEpsilons e.Target
                            else
                                pFun e.Tag (e.Target * 1<positionInInput>)
                    )
            
            forAllOutgoingEdgesAndEpsilons (int curPosInInput)

        member this.PositionToString (pos : int<positionInInput>) =
            sprintf "%i" pos

type TokenLabeledInputSubGraph(basicGraph: TokenLabeledInputGraph, initialPostitions: int<positionInInput>[]) =
    interface IParserInput with
        member this.InitialPositions = 
            initialPostitions
        
        member this.FinalPositions = 
            (basicGraph :> IParserInput).FinalPositions

        member this.ForAllOutgoingEdges curPosInInput pFun = 
            (basicGraph :> IParserInput).ForAllOutgoingEdges curPosInInput pFun

        member this.PositionToString (pos : int<positionInInput>) =
            sprintf "%i" pos

module Parsing =
    open System.Threading
    open FSharpx.Collections
    open System.Threading.Tasks
    open QuickGraph

    let generateParser calls locks asserts =
        let time = System.DateTime.UtcNow
        Logging.stage "Automata construction"
        
        let calls = if (calls < 2) then 2 else calls
        let locks = if (locks < 2) then 2 else locks
        let asserts = if (asserts < 2) then 2 else asserts
        
        let factory = new AutomataFactory()
        let (~%%), (~&&), (~%), (~&), eps, (=>), (!=>), (<~>), (<|>) = factory.Combinators
    
        let assertTokens =  [|0..asserts - 1|] 
                            |> Array.map ((sprintf "A%i") >> factory.TerminalToken)
        
        let holeTokens =    [|0..calls - 1|]
                            |> Array.map ((sprintf "H%i") >> factory.TerminalToken)
    
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
        
        let holes() = [0..calls - 1]
                      |> List.map (fun i -> %holeTokens.[i])
                      |> factory.Alternations
        
        let brackets count (left: EdgeSymbol list) body (right: EdgeSymbol list) =
            List.zip left right
            |> List.map (fun (left, right) -> (%left <~> &body <~> %right))
            |> factory.Alternations
        
        let brackets2 count (left: EdgeSymbol list) body (right: EdgeSymbol list) =
            List.zip left right
            |> List.map (fun (left, right) -> (%left <~> ((%right) <|> (&body <~> %right))))
            |> factory.Alternations
        
        let ba = &&"ba"
        let ca = &&"ca"
        let s0 = &&"s0"
        let s0i = &&"s0i"
        let s1 = &&"s1"
        let ss = &&"ss"
        let s = &&"s"
        
        "ba" => asserts
        "ca" => asserts
        "s0i" => ((%(%%"I") <|> &ca <|> &s0) <~> (&s0i <|> eps))
        "s0" => (brackets2 locks getTokens s0i releaseTokens)
        "s1" => ((%(%%"I") <|> &s0) <~> (&s1 <|> eps))
        "ss" => ((&ba <|> (brackets calls callTokens s returnTokens)))
        "s" !=> (((&s1 <~> &ss) <|> &ss) <~> (&s1 <|> eps))
    
        (*
        "ba" => asserts
        "ca" => asserts
        "s0" => ((    ((brackets2 calls callTokens s0 returnTokens) 
                  <|> (brackets2 locks getTokens s0 releaseTokens)) <~> (&s0 <|> eps))
                 <|> (&ca <~> (&s0 <|> eps)))
        "s1" => ((    ((brackets2 calls callTokens s1 returnTokens) 
                  <|> (brackets2 locks getTokens s0 releaseTokens)) <~> (&s1 <|> eps)))
        "s" !=> (((brackets calls callTokens s returnTokens) <~> (&s <|> eps))
                 <|> (&s <~> (&s1 <|> &ba))
                 <|> (&s1 <~> &s)
                 <|> (&ba <~> (&s <|> eps)))
                 *)
                 (*
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
                 *)
    
        Logging.log (sprintf "Automata construction time is %A" (System.DateTime.UtcNow - time))
    
        let time = System.DateTime.UtcNow
        Logging.stage "Automata conversion"

        let automata = factory.Produce()
        automata.PrintDot "test.dot"

        Logging.log (sprintf "Automata conversion time is %A" (System.DateTime.UtcNow - time))

        let time = System.DateTime.UtcNow
        Logging.stage "Parser generation"

        let gll = new GLL()
        let parser = gll.GenerateFromFSA automata false "gll.fs" :?> ParserSourceGLL

        Logging.log (sprintf "Parser generation time is %A" (System.DateTime.UtcNow - time))

        parser
    
    let parseAbstractInputsAsync parserSource (inputs: IParserInput []) =
        let tokenSource = new CancellationTokenSource()
        let token = tokenSource.Token
        
        let tasks = 
            inputs
            |> Array.map
                (
                    fun input ->
                        let task = 
                            Task.Factory.StartNew (
                                fun () -> 
                                    getAllSPPFRootsAsINodesInterruptable parserSource input (fun () -> token.IsCancellationRequested)
                            )
                        task
                )
                
        let finalTask = Task.Factory.ContinueWhenAll(tasks, Array.collect (fun (task: Task<_>) -> task.Result), token)
        
        finalTask, tokenSource
        
    let parseGraph parserSource (inputGraph: TokenLabeledInputGraph) (components: int [] []) =
        let parallelTasks = min 2 components.Length
        let chunkSize = components.Length / parallelTasks 
        
        let tasks = [|0..parallelTasks - 1|]
                    |> Array.map
                        (
                            fun id ->
                                let task = 
                                    Task.Factory.StartNew (
                                        fun () -> 
                                            let subArraySize = min (components.Length - (id * chunkSize)) chunkSize
                                            let starts = 
                                                Array.sub components (id * chunkSize) subArraySize 
                                                |> Array.concat
                                                |> Array.map ((*) 1<positionInInput>)
                                            let subgraph = new TokenLabeledInputSubGraph (inputGraph, starts)
                                            getAllSPPFRootsAsINodes parserSource subgraph
                                    )
                                task
                        )
        
        let results = 
            tasks 
            |> Array.collect 
                (
                    fun task ->
                        task.Wait()
                        task.Result
                )
        
        results
