using System;

namespace Sparrow.Json.Parsing
{
    public interface IJsonParser : IDisposable
    {
        bool Read();
        void ValidateFloat();
        string GenerateErrorState();
    }

    public interface IJsonParserDispatcher<out T> where T : IJsonParser
    {
        T Parser { get; }
    }
}
