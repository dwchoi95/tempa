// Console driver around the original Refazer (Refazer4Python), unchanged.
//
//   mono Refazer.exe learn <pairs.json> <out_dir>
//       pairs.json: [{"id": "...", "before": "...", "after": "..."}, ...]
//       For each pair separately: LearnTransformations([pair]) (top-1, "specific"
//       ranking: Refazer's defaults), write the program to <out_dir>/<id>.json,
//       and print one JSON log line per pair on stdout: {"id", "ok", "seconds", "error"}.
//   mono Refazer.exe serve <out_dir> [timeout_seconds=5]
//       Loads every <out_dir>/<id>.json (id = integer rule index), then reads JSON
//       lines {"rule": k, "source": text[, "seq": n]} from stdin and writes one JSON
//       line {"outputs": [...], "seq": n} per request: every program Apply
//       returns, or [] on a missing rule, parse error, exception or timeout.
//
// Persistence: PROSE's XML AST format prints Refazer's NodeInfo literals with
// ToString ("ConstantExpressionNode-1": int or str?) and cannot parse them back,
// so programs are stored as a JSON tree of grammar rules with type-tagged
// literals. A learned program is kept only if it reloads Equal to itself.
//
// Library code may write to Console.Out, so the protocol uses the raw stdout
// stream and Console.Out is pointed at stderr.
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Text;
using System.Threading;
using Microsoft.ProgramSynthesis;
using Microsoft.ProgramSynthesis.AST;
using Microsoft.ProgramSynthesis.Rules;
using Newtonsoft.Json;
using Newtonsoft.Json.Linq;
using Refazer.Core;
using Tutor;

static class Driver
{
    static readonly UTF8Encoding Utf8 = new UTF8Encoding(false);
    static readonly JsonSerializerSettings Raw = new JsonSerializerSettings { DateParseHandling = DateParseHandling.None };
    static readonly CultureInfo Inv = CultureInfo.InvariantCulture;
    static TextWriter Proto;

    static Refazer4Python Make()
    {
        var dir = AppDomain.CurrentDomain.BaseDirectory;   // Transformation.grammar and Tutor.dll live here
        var r = new Refazer4Python(dir, dir);
        if (r.Grammar.Value == null)
            throw new Exception("grammar failed to compile: " + string.Join("; ", r.Grammar.Diagnostics));
        return r;
    }

    static void Emit(object o) { Proto.WriteLine(JsonConvert.SerializeObject(o)); Proto.Flush(); }

    static int Main(string[] args)
    {
        Proto = new StreamWriter(Console.OpenStandardOutput(), Utf8);
        Console.SetOut(Console.Error);
        if (args.Length >= 3 && args[0] == "learn") return Learn(args[1], args[2]);
        if (args.Length >= 2 && args[0] == "serve") return Serve(args[1], args.Length > 2 ? double.Parse(args[2], Inv) : 5.0);
        Console.Error.WriteLine("usage: Refazer.exe learn <pairs.json> <out_dir> | serve <out_dir> [timeout_s]");
        return 2;
    }

    // ---- program (de)serialization -------------------------------------------------

    static JToken Value(object v)
    {
        if (v == null) return null;
        var t = v.GetType();
        string s;
        if (v is Complex) { var c = (Complex)v; s = c.Real.ToString("R", Inv) + " " + c.Imaginary.ToString("R", Inv); }
        else if (v is double) s = ((double)v).ToString("R", Inv);
        else if (v is BigInteger || t.IsEnum || v is string || v is IConvertible) s = Convert.ToString(v, Inv);
        else throw new NotSupportedException("literal of type " + t.FullName);
        return new JObject { ["t"] = t.AssemblyQualifiedName, ["s"] = s };
    }

    static object Unvalue(JToken j)
    {
        if (j == null || j.Type == JTokenType.Null) return null;
        var t = Type.GetType((string)j["t"], true);
        var s = (string)j["s"];
        if (t == typeof(Complex)) { var p = s.Split(' '); return new Complex(double.Parse(p[0], Inv), double.Parse(p[1], Inv)); }
        if (t == typeof(BigInteger)) return BigInteger.Parse(s, Inv);
        if (t.IsEnum) return Enum.Parse(t, s);
        return Convert.ChangeType(s, t, Inv);
    }

    static JToken Save(ProgramNode n)
    {
        var lam = n as LambdaNode;   // the \node => ... of Map/Filter; its rule has no id
        if (lam != null) return new JObject { ["lam"] = n.Symbol.Name, ["b"] = Save(lam.BodyNode) };
        var nt = n as NonterminalNode;
        if (nt != null) return new JObject { ["r"] = nt.Rule.Id, ["c"] = new JArray(nt.Children.Select(Save)) };
        if (n is VariableNode) return new JObject { ["v"] = n.Symbol.Name };
        var lit = n as LiteralNode;
        if (lit == null) throw new NotSupportedException("AST node " + n.GetType().Name);
        var info = lit.Value as NodeInfo;
        return info != null
            ? new JObject { ["l"] = n.Symbol.Name, ["info"] = info.NodeType, ["val"] = Value((object)info.NodeValue) }
            : new JObject { ["l"] = n.Symbol.Name, ["val"] = Value(lit.Value) };
    }

    static ProgramNode Load(JToken j, Grammar g)
    {
        if (j["lam"] != null)
            return new LambdaNode((LambdaRule)g.RulesOfHead((string)j["lam"]).Single(), Load(j["b"], g));
        if (j["r"] != null)
            return new NonterminalNode((NonterminalRule)g.Rule((string)j["r"]), j["c"].Select(c => Load(c, g)).ToArray());
        if (j["v"] != null) return new VariableNode(g.Symbol((string)j["v"]));
        var val = Unvalue(j["val"]);
        return new LiteralNode(g.Symbol((string)j["l"]),
            j["info"] != null ? (val == null ? new NodeInfo((string)j["info"]) : new NodeInfo((string)j["info"], val)) : val);
    }

    // ---- modes ---------------------------------------------------------------------

    static int Learn(string pairsPath, string outDir)
    {
        Directory.CreateDirectory(outDir);
        var pairs = JsonConvert.DeserializeObject<JArray>(File.ReadAllText(pairsPath, Utf8), Raw);
        var refazer = Make();
        var g = refazer.Grammar.Value;
        foreach (var p in pairs)
        {
            var id = (string)p["id"];
            var sw = Stopwatch.StartNew();
            string error = null;
            try
            {
                var examples = new List<Tuple<string, string>> { Tuple.Create((string)p["before"], (string)p["after"]) };
                var t = refazer.LearnTransformations(examples).FirstOrDefault();
                if (t == null) error = "no program learned";
                else
                {
                    var prog = t.GetSynthesizedProgram();
                    var json = Save(prog).ToString(Formatting.None);
                    if (!Load(JToken.Parse(json), g).Equals(prog)) error = "program does not round-trip";
                    else File.WriteAllText(Path.Combine(outDir, id + ".json"), json, Utf8);
                }
            }
            catch (Exception e)
            {
                var frame = (e.StackTrace ?? "").Split('\n')[0].Trim();   // where in Refazer it gave up
                error = e.GetType().Name + ": " + e.Message + " | " + frame;
            }
            Emit(new { id, ok = error == null, seconds = Math.Round(sw.Elapsed.TotalSeconds, 3), error });
        }
        return 0;
    }

    static int Serve(string dir, double timeout)
    {
        var sw = Stopwatch.StartNew();
        var refazer = Make();
        var rules = new Dictionary<int, PythonTransformation>();
        foreach (var f in Directory.GetFiles(dir, "*.json"))
        {
            int k;
            if (!int.TryParse(Path.GetFileNameWithoutExtension(f), out k)) continue;
            try { rules[k] = new PythonTransformation(Load(JToken.Parse(File.ReadAllText(f, Utf8)), refazer.Grammar.Value)); }
            catch (Exception e) { Console.Error.WriteLine("refazer serve: cannot load " + f + ": " + e.Message); }
        }
        Console.Error.WriteLine("refazer serve: loaded " + rules.Count + " transformations in " + sw.Elapsed.TotalSeconds.ToString("F2", Inv) + " s");
        var stdin = new StreamReader(Console.OpenStandardInput(), Utf8);
        string line;
        while ((line = stdin.ReadLine()) != null)
        {
            if (line.Trim().Length == 0) continue;
            JToken seq = null;
            var outputs = new List<string>();
            try
            {
                var req = JsonConvert.DeserializeObject<JObject>(line, Raw);
                seq = req["seq"];
                PythonTransformation t;
                if (rules.TryGetValue((int)req["rule"], out t))
                {
                    var src = (string)req["source"];
                    List<string> result = null;
                    // Own thread: a hung Apply is abandoned after `timeout`; big stack
                    // because Refazer's tree code recurses once per AST level.
                    var th = new Thread(() =>
                    {
                        try { result = refazer.Apply(t, src).ToList(); }
                        catch (Exception e) { Console.Error.WriteLine("refazer serve: apply: " + e.GetType().Name + ": " + e.Message); }
                    }, 256 << 20);
                    th.IsBackground = true;
                    th.Start();
                    if (th.Join(TimeSpan.FromSeconds(timeout))) { if (result != null) outputs = result; }
                    else { try { th.Abort(); } catch (Exception) { } }
                }
            }
            catch (Exception e) { Console.Error.WriteLine("refazer serve: bad request: " + e.Message); }
            Emit(new { outputs, seq });
        }
        return 0;
    }
}
