using System.Collections.Generic;

namespace CfrAnalysisTemplate
{
    public interface IAutomatonPart
    {
    }
    
    public interface IToken
    {
    }

    public interface IAutomataFactory
    {
        IToken TerminalToken(string name);
        IToken NonterminalToken(string name);

        IAutomatonPart Terminal(IToken token);
        IAutomatonPart Reference(IToken token);
        IAutomatonPart Final();

        IAutomatonPart Sequence(IAutomatonPart left, IAutomatonPart right);
        IAutomatonPart Alternation(IAutomatonPart left, IAutomatonPart right);
        IAutomatonPart Alternations(IEnumerable<IAutomatonPart> parts);

        void Rule(string name, IAutomatonPart body);
        void Start(string name, IAutomatonPart body);
    }

    public interface IGraphStatistics
    {
    }

    public interface ICfrAnalysis
    {
        IGraphStatistics InitStatistics();
        void AddEdgeToStatistics(IGraphStatistics statistics, string label);

        void ConstructAutomaton(IAutomataFactory factory, IGraphStatistics statistics);
    }
}