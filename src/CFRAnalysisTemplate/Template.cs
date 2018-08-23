using System.Collections.Generic;
using System.Runtime.CompilerServices;

namespace CfrAnalysisTemplate
{
    public static class FactoryHolder
    {
        public static IAutomataFactory Factory;

        public static void SetFactory(IAutomataFactory factory)
        {
            Factory = factory;
        }
    }

    public abstract class AutomatonPart
    {
        public static AutomatonPart operator -(AutomatonPart left, AutomatonPart right)
        {
            return FactoryHolder.Factory.Sequence(left, right);
        }

        public static AutomatonPart operator |(AutomatonPart left, AutomatonPart right)
        {
            return FactoryHolder.Factory.Alternation(left, right);
        }

        public static bool operator >=(string name, AutomatonPart body)
        {
            FactoryHolder.Factory.Rule(name, body);
            return true;
        }

        public static bool operator <=(string name, AutomatonPart body)
        {
            FactoryHolder.Factory.Start(name, body);
            return true;
        }
    }

    public abstract class Token
    {
        public static AutomatonPart operator !(Token token)
        {
            return FactoryHolder.Factory.Terminal(token);
        }

        public static AutomatonPart operator ~(Token token)
        {
            return FactoryHolder.Factory.Reference(token);
        }
    }

    public interface IAutomataFactory
    {
        Token TerminalToken(string name);
        Token NonterminalToken(string name);

        AutomatonPart Terminal(Token token);
        AutomatonPart Reference(Token token);
        AutomatonPart Final();

        AutomatonPart Sequence(AutomatonPart left, AutomatonPart right);
        AutomatonPart Alternation(AutomatonPart left, AutomatonPart right);
        AutomatonPart Alternations(IEnumerable<AutomatonPart> parts);

        void Rule(string name, AutomatonPart body);
        void Start(string name, AutomatonPart body);
    }

    public interface IGraphStatistics
    {
    }

    public interface ICfrAnalysis
    {
        IGraphStatistics InitStatistics();
        void AddEdgeToStatistics(IGraphStatistics statistics, string label);
        void RemoveEdgeFromStatistics(IGraphStatistics statistics, string label);
        void ConstructAutomaton(IGraphStatistics statistics);
    }
}