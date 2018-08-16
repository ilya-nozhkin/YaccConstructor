namespace LockChecker

open System.IO
open System.Net
open System.Net.Sockets
open System.Runtime.Serialization.Json
open System.Runtime.Serialization
open System.Collections.Generic
open System.Threading.Tasks

open LockChecker.Graph

[<DataContract>]
type AddMethodMessage =
    {
        [<field: DataMember(Name="method")>]
        method: Method
        
        [<field: DataMember(Name="edges")>]
        edges: RawEdge []
    }
    static member JsonReader = DataContractJsonSerializer(typeof<AddMethodMessage>)
    static member FromJson (source: Stream) =
        AddMethodMessage.JsonReader.ReadObject(source) :?> AddMethodMessage

[<DataContract>]
type UpdateFileMessage =
    {
        [<field: DataMember(Name="fileName")>]
        fileName: string
        
        [<field: DataMember(Name="methods")>]
        methods: string []
    }
    static member JsonReader = DataContractJsonSerializer(typeof<UpdateFileMessage>)
    static member FromJson (source: Stream) =
        UpdateFileMessage.JsonReader.ReadObject(source) :?> UpdateFileMessage

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
type UpdateDelegateParameterMessage = 
    struct end
    static member JsonReader = DataContractJsonSerializer(typeof<DelegateParameterInfo>)
    static member FromJson (source: Stream) =
        UpdateDelegateParameterMessage.JsonReader.ReadObject(source) :?> DelegateParameterInfo

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

type ServiceHost(graphProvider: unit -> ControlFlowGraph, port) =
    let socket = TcpListener.Create (port)
    let mutable client = null
    let mutable isProcess = true
    
    let mutable graph: ControlFlowGraph = graphProvider()
    
    let mutable asyncReadTask = null
    
    let mutable mostRecentlyUpdatedFile: string = null
        
    let performParsing (reader: StreamReader) (writer: StreamWriter) (startFile: string) =
        let statistics = graph.GetStatistics()
        let parserSource = Parsing.generateParser statistics.calls statistics.locks statistics.asserts
        
        let parallelTasks = 2
        let inputs = graph.GetParserInput startFile parserSource.StringToToken
        
        let task, cancellation = Parsing.parseAbstractInputsAsync parserSource [|inputs|]
        
        let asyncMessage = reader.ReadLineAsync()
        let asyncCanceller = 
            asyncMessage.ContinueWith (
                fun (completed: Task<_>) -> 
                    if completed.Result = "interrupt" then cancellation.Cancel()
            )
            
        asyncReadTask <- asyncCanceller
        
        if asyncCanceller.Status = TaskStatus.Created then
            asyncCanceller.Start()
        
        task.Wait()
        
        let roots = task.Result
        
        let results = 
            let temporaryResults = new HashSet<_>()
            roots
            |> Array.map (fun x -> ResultProcessing.extractNonCyclicPaths x parserSource.IntToString)
            |> Array.iter (fun s -> temporaryResults.UnionWith s)
            temporaryResults
        
        results |> Seq.iter (writer.WriteLine)
        writer.Flush()
    
    member this.Start() =
        socket.Start()
        client <- socket.AcceptTcpClient()
        
        use stream = client.GetStream()
        use reader = new StreamReader(stream)
        use writer = new StreamWriter(stream)
        
        while isProcess do
            if asyncReadTask <> null then
                asyncReadTask.Wait()
                asyncReadTask <- null
                
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
                    let message = AddMethodMessage.FromJson dataStream
                    graph.EnqueueMethodForProcessing (message.method) (message.edges)
                    success <- true
                | "update_file" ->
                    let message = UpdateFileMessage.FromJson dataStream
                    graph.UpdateFileInfo (message.fileName) (set message.methods)
                    mostRecentlyUpdatedFile <- message.fileName
                    success <- true
                | "add_edge_pack" -> 
                    let message = AddEdgePackMessage.FromJson dataStream
                    graph.AddEdgePack message.edges
                    success <- true
                | "update_decoder" -> 
                    let message = UpdateDecoderMessage.FromJson dataStream
                    message.records |> Array.iter (fun record -> ResultProcessing.decoder.[record.code] <- record.data)
                    success <- true
                | "update_delegate_parameter" ->
                    let message = UpdateDelegateParameterMessage.FromJson dataStream
                    graph.UpdateDelegateParameter message
                    success <- true
                | "run_analysis" ->
                    let message = RunAnalysisMessage.FromJson dataStream
                    if mostRecentlyUpdatedFile = null then
                        asyncReadTask <- reader.ReadLineAsync();
                    else
                        performParsing reader writer mostRecentlyUpdatedFile
                    success <- true
                | "dump_graph" ->
                    graph.DumpStatesLevel writer
                    success <- true
                | "terminate" ->
                    (*
                    use fileStream = new FileStream ("graph.dump", FileMode.Create)
                    graph.Serialize fileStream
                    *)
                    
                    isProcess <- false
                    success <- true
                | "reset" ->
                    graph <- graphProvider()
                    success <- true
                | _ -> ()
            with e -> printfn "%s\r\n%s" e.Message e.StackTrace
            
            if success then
                writer.WriteLine("success")
                printfn "success"
            else
                writer.WriteLine("failure")
                printfn "failure"
                
            writer.Flush()
                
        client.Close()
        socket.Stop()           
        
        
        
        
        
