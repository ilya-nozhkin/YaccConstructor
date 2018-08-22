namespace CfrAnalyser

module Analysis =
    open System.Reflection
    open CfrAnalysisTemplate

    let assembly = Assembly.LoadFrom("Template.dll")
    let instance = assembly.CreateInstance("CfrAnalysis.CfrAnalysis") :?> ICfrAnalysis
