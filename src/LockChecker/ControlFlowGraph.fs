namespace LockChecker.Graph

open AbstractAnalysis.Common
open System
open System.Collections.Generic
open System.Diagnostics

open System.Collections.Generic
open System.IO
open QuickGraph
open System.Runtime.Serialization
open System.Runtime.CompilerServices

[<DataContract>]
type Method =
    {
        [<field: DataMember(Name="name")>]
        name: string
        
        [<field: DataMember(Name="startNode")>]
        startNode: int
        
        [<field: DataMember(Name="finalNodes")>]
        finalNodes: int []
    }
    
[<DataContract>]
type RawEdge = 
    {
        [<field: DataMember(Name="s")>]
        startNode: int
        
        [<field: DataMember(Name="l")>]
        label: string
        
        [<field: DataMember(Name="t")>]
        endNode: int
    }

type GraphStatistics =
    {
        nodes: int
        calls: int
        locks: int
        asserts: int
    }
    
type IControlFlowGraph =
    abstract member Serialize: Stream -> unit
    abstract member Deserialize: Stream -> unit
    
    abstract member AddMethod: Method -> RawEdge [] -> unit
    abstract member AlterMethod: Method -> RawEdge [] -> unit
    abstract member RemoveMethod: string -> unit
    
    abstract member UpdateFileInfo: string -> Set<string> -> unit
    abstract member GetFileInfo: string -> Set<string>
    
    abstract member AddEdges: RawEdge [] -> unit
   
    abstract member GetStatistics: unit -> GraphStatistics
    
    abstract member PrepareForParsing: unit -> unit
    abstract member CleanUpAfterParsing: unit -> unit
    
    abstract member SetTokenizer: (string -> int<token>) -> unit
    abstract member SetStarts: int [] [] -> unit
    
    abstract member GetParserInputs: int -> IParserInput []
