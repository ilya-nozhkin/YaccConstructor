namespace CfrAnalyser

module Logging =
    let mutable log: string -> unit =
        fun message ->
            printfn "%s" message
            
    let mutable stage: string -> unit =
        fun message ->
            printfn "%s" message