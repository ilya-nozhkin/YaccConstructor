namespace LockChecker

open System.IO
open System.Net
open System.Net.Sockets
open System.Runtime.Serialization.Json
open System.Runtime.Serialization
open System.Collections.Generic

open LockChecker.Graph

[<DataContract>]
type NewMethodMessage =
    {
        [<field: DataMember(Name="method")>]
        method: Method
        
        [<field: DataMember(Name="edges")>]
        edges: RawEdge []
    }
    static member JsonReader = DataContractJsonSerializer(typeof<NewMethodMessage>)
    static member FromJson (source: Stream) =
        NewMethodMessage.JsonReader.ReadObject(source) :?> NewMethodMessage
        
[<DataContract>]
type MethodChangedMessage =
    {
        [<field: DataMember(Name="method")>]
        method: Method
        
        [<field: DataMember(Name="edges")>]
        edges: RawEdge []
    }
    static member JsonReader = DataContractJsonSerializer(typeof<MethodChangedMessage>)
    static member FromJson (source: Stream) =
        MethodChangedMessage.JsonReader.ReadObject(source) :?> MethodChangedMessage
        
[<DataContract>]
type MethodRemovedMessage =
    {
        [<field: DataMember(Name="name")>]
        name: string
    }
    static member JsonReader = DataContractJsonSerializer(typeof<MethodRemovedMessage>)
    static member FromJson (source: Stream) =
        MethodRemovedMessage.JsonReader.ReadObject(source) :?> MethodRemovedMessage

[<DataContract>]
type AddEdgePackMessage =
    {
        [<field: DataMember(Name="edges")>]
        edges: RawEdge []
    }
    static member JsonReader = DataContractJsonSerializer(typeof<AddEdgePackMessage>)
    static member FromJson (source: Stream) =
        AddEdgePackMessage.JsonReader.ReadObject(source) :?> AddEdgePackMessage

[<DataContract>]
type RunAnalysisMessage =
    {
        [<field: DataMember(Name="starts")>]
        starts: int [] []
    }
    static member JsonReader = DataContractJsonSerializer(typeof<RunAnalysisMessage>)
    static member FromJson (source: Stream) =
        RunAnalysisMessage.JsonReader.ReadObject(source) :?> RunAnalysisMessage
        
[<DataContract>]
type DecoderRecord =
    {
        [<field: DataMember(Name="code")>]
        code: string
        
        [<field: DataMember(Name="data")>]
        data: string
    }

[<DataContract>]
type UpdateDecoderMessage =
    {
        [<field: DataMember(Name="records")>]
        records: DecoderRecord []
    }
    static member JsonReader = DataContractJsonSerializer(typeof<UpdateDecoderMessage>)
    static member FromJson (source: Stream) =
        UpdateDecoderMessage.JsonReader.ReadObject(source) :?> UpdateDecoderMessage

type ServiceHost(graphProvider: unit -> IControlFlowGraph, port) =
    let socket = TcpListener.Create (port)
    let mutable client = null
    let mutable isProcess = true
    let mutable graph: IControlFlowGraph = graphProvider()
    
    let performParsing (writer : StreamWriter) =
        let statistics = graph.GetStatistics()
        let parserSource = Parsing.generateParser statistics.calls statistics.locks statistics.asserts
        graph.SetTokenizer parserSource.StringToToken
        
        graph.PrepareForParsing()
        
        let parallelTasks = 2
        let inputs = graph.GetParserInputs parallelTasks
        
        let roots = Parsing.parseAbstractInputsParallel parserSource inputs
        
        let results = 
            let temporaryResults = new HashSet<_>()
            roots
            |> Array.map (fun x -> ResultProcessing.extractNonCyclicPaths x parserSource.IntToString)
            |> Array.iter (fun s -> temporaryResults.UnionWith s)
            temporaryResults
        
        results |> Seq.iter (writer.WriteLine)
        
        graph.CleanUpAfterParsing()
    
    member this.Start() =
        socket.Start()
        client <- socket.AcceptTcpClient()
        
        use stream = client.GetStream()
        use reader = new StreamReader(stream)
        use writer = new StreamWriter(stream)
        
        while isProcess do
            let mutable messageType = reader.ReadLine()
            let mutable data = reader.ReadLine()
            let mutable success = false
            
            if messageType = null then 
                messageType <- "terminate"
                data <- ""
            
            printfn "incoming message:"
            printfn "%s" messageType
            printfn "%s" data
            
            try
                use dataStream = new MemoryStream(System.Text.Encoding.ASCII.GetBytes(data))
                match messageType with
                | "add_method" -> 
                    let message = NewMethodMessage.FromJson dataStream
                    graph.AddMethod message.method message.edges
                    success <- true
                | "alter_method" -> 
                    let message = MethodChangedMessage.FromJson dataStream
                    graph.AlterMethod message.method message.edges
                    success <- true
                | "add_edge_pack" -> 
                    let message = AddEdgePackMessage.FromJson dataStream
                    graph.AddEdges message.edges
                    success <- true
                | "remove_method" -> 
                    let message = MethodRemovedMessage.FromJson dataStream
                    graph.RemoveMethod message.name
                    success <- true
                | "update_decoder" -> 
                    let message = UpdateDecoderMessage.FromJson dataStream
                    message.records |> Array.iter (fun record -> ResultProcessing.decoder.[record.code] <- record.data)
                    success <- true
                | "run_analysis" ->
                    let message = RunAnalysisMessage.FromJson dataStream
                    graph.SetStarts message.starts
                    performParsing writer
                    success <- true
                | "terminate" ->
                    use fileStream = new FileStream ("graph.dump", FileMode.Create)
                    graph.Serialize fileStream
                    
                    isProcess <- false
                    success <- true
                | "reset" ->
                    graph <- graphProvider()
                    success <- true
                | _ -> ()
            with e -> printfn "%s" e.Message
            
            if success then
                writer.WriteLine("success")
                printfn "success"
            else
                writer.WriteLine("failure")
                printfn "failure"
                
            writer.Flush()
                
        client.Close()
        socket.Stop()           
        
        
        
        
        
