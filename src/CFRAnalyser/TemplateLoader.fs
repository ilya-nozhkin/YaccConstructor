namespace CfrAnalyser

module Analysis =
    open System.Reflection
    open CfrAnalysisTemplate

    let mutable assembly = null
    let mutable instance = null

    let setFactory (factory: IAutomataFactory) = FactoryHolder.SetFactory factory

    let loadDll path =
        Logging.log ("Loading analysis from: " + path)
        assembly <- Assembly.LoadFrom(path)
        instance <- assembly.CreateInstance("CfrAnalysis.CfrAnalysis") :?> ICfrAnalysis
        Logging.log ("Analysis loaded")