namespace CfrAnalyser

open Yard.Generators.GLL
open Yard.Generators.GLL.ParserCommon
open Yard.Generators.Common.AutomataCombinators
open Yard.Generators.Common.FSA.Common
open AbstractAnalysis.Common
open QuickGraph

open AbstractParser

open CfrAnalysisTemplate

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
    open CfrAnalyser

    type TokenAdapter(token) =
        inherit Token()
        member this.Token = token

    type AutomatonPartAdapter(part) =
        inherit AutomatonPart()
        member this.AutomatonPart = part

    type AutomataFactoryAdapter() =
        let internalFactory = new AutomataFactory()
        let epsilon = AutomatonPartAdapter(internalFactory.Epsilon) :> AutomatonPart

        member this.Produce() = 
            internalFactory.Produce()

        interface IAutomataFactory with
            member this.TerminalToken name =
                TokenAdapter(internalFactory.TerminalToken name) :> Token

            member this.NonterminalToken name =
                TokenAdapter(internalFactory.NonterminalToken name) :> Token

            member this.Terminal token =
                AutomatonPartAdapter(internalFactory.Terminal (token :?> TokenAdapter).Token) :> AutomatonPart

            member this.Reference token =
                AutomatonPartAdapter(internalFactory.Reference (token :?> TokenAdapter).Token) :> AutomatonPart

            member this.Final() =
                epsilon

            member this.Sequence(left, right) =
                AutomatonPartAdapter(internalFactory.Sequence ((left :?> AutomatonPartAdapter).AutomatonPart) ((right :?> AutomatonPartAdapter).AutomatonPart)) :> AutomatonPart

            member this.Alternation(left, right) =
                AutomatonPartAdapter(internalFactory.Alternation ((left :?> AutomatonPartAdapter).AutomatonPart) ((right :?> AutomatonPartAdapter).AutomatonPart)) :> AutomatonPart

            member this.Alternations(parts) =
                AutomatonPartAdapter(internalFactory.Alternations (parts |> Seq.map (fun part -> (part :?> AutomatonPartAdapter).AutomatonPart) |> Seq.toList)) :> AutomatonPart

            member this.Rule(name, body) =
                internalFactory.Rule name (body :?> AutomatonPartAdapter).AutomatonPart

            member this.Start(name, body) =
                internalFactory.Start name (body :?> AutomatonPartAdapter).AutomatonPart

    let generateParser (statistics: IGraphStatistics) =
        let factory = new AutomataFactoryAdapter()
        Analysis.setFactory (factory :> IAutomataFactory)

        Analysis.instance.ConstructAutomaton(statistics)

        let automata = factory.Produce()

        let gll = new GLL()
        let parser = gll.GenerateFromFSA automata false "gll.fs" :?> ParserSourceGLL

        parser
    
    let parseAsync (parser: GLLParser) (starts: int<positionInInput> []) =
        let tokenSource = new CancellationTokenSource()
        let token = tokenSource.Token
        
        let task = 
            Task.Factory.StartNew (
                (
                    fun () -> 
                        try
                            parser.ParseMore starts (fun () -> token.IsCancellationRequested)
                        with e ->
                            printfn "%s" e.Message
                            printfn "%s" e.StackTrace
                            raise e
                ), token) 
                
        task, tokenSource
        
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
                                            (new GLLParser(parserSource, subgraph, true)).GetAllSPPFRootsAsINodes()
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
