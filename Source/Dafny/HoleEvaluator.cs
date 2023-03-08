//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System;
using System.Text;
using System.IO;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Diagnostics;
using System.Reflection;
using System.Linq;
using Microsoft.Boogie;
using System.Threading.Tasks;

namespace Microsoft.Dafny {
  public enum Result {
    Unknown = 0,
    CorrectProof = 1,
    CorrectProofByTimeout = 2,
    IncorrectProof = 3,
    FalsePredicate = 4,
    InvalidExpr = 5,
    NoMatchingTrigger = 6
  }
  public class HoleEvaluator {
    private string UnderscoreStr = "";
    private static Random random = new Random();

    public static string RandomString(int length) {
      const string chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
      return new string(Enumerable.Repeat(chars, length)
          .Select(s => s[random.Next(s.Length)]).ToArray());
    }
    public ExpressionFinder expressionFinder = null;
    private List<BitArray> bitArrayList = new List<BitArray>();
    private List<float> executionTimes = new List<float>();
    private List<float> startTimes = new List<float>();
    private Expression constraintExpr = null;

    public static bool IsGoodResult(Result result) {
      return (result == Result.CorrectProof ||
              result == Result.CorrectProofByTimeout ||
              result == Result.IncorrectProof ||
              result == Result.Unknown);
    }
    private Dictionary<int, Result> combinationResults = new Dictionary<int, Result>();
    private Dictionary<int, int> negateOfExpressionIndex = new Dictionary<int, int>();
    // private DafnyExecutor dafnyMainExecutor = new DafnyExecutor();
    private DafnyExecutor dafnyImpliesExecutor = new DafnyExecutor();
    private DafnyVerifierClient dafnyVerifier;

    private TasksList tasksList = null;
    private IncludeParser includeParser = null;
    private List<string> affectedFiles = new List<string>();

    public static int validityLemmaNameStartCol = 0;

    private void UpdateCombinationResult(int index) {
      var request = dafnyVerifier.requestsList[index];
      var position = dafnyVerifier.requestToPostConditionPosition[request];
      var lemmaStartPosition = dafnyVerifier.requestToLemmaStartPosition[request];
      var output = dafnyVerifier.dafnyOutput[request];
      var response = output.Response;
      var filePath = output.FileName;
      var startTime = output.StartTime;
      var execTime = output.ExecutionTime;
      executionTimes.Add(execTime);
      startTimes.Add(startTime);
      var expectedOutput =
        $"{filePath}({position},0): Error: A postcondition might not hold on this return path.";
      var expectedInconclusiveOutputStart =
        $"{filePath}({lemmaStartPosition},{validityLemmaNameStartCol}): Verification inconclusive";
      // Console.WriteLine($"{index} => {output}");
      // Console.WriteLine($"{output.EndsWith("0 errors\n")} {output.EndsWith($"resolution/type errors detected in {fileName}.dfy\n")}");
      // Console.WriteLine($"----------------------------------------------------------------");
      var res = DafnyVerifierClient.IsCorrectOutput(response, expectedOutput, expectedInconclusiveOutputStart);
      if (res != Result.IncorrectProof) {
        // correctExpressions.Add(dafnyMainExecutor.processToExpr[p]);
        // Console.WriteLine(output);
        combinationResults[index] = res;
        // Console.WriteLine(p.StartInfo.Arguments);
        Console.WriteLine(Printer.ExprToString(dafnyVerifier.requestToExpr[request]));
      } else if (response.EndsWith(" 0 errors\n")) {
        combinationResults[index] = Result.FalsePredicate;
        Console.WriteLine("Mutation that Passes = " + index);
      } else if (response.EndsWith($"resolution/type errors detected in {Path.GetFileName(filePath)}\n")) {
        combinationResults[index] = Result.InvalidExpr;
      } else {
        combinationResults[index] = Result.IncorrectProof;
      }
      expressionFinder.combinationResults[index] = combinationResults[index];
    }

    public Dictionary<string, List<string>> GetEqualExpressionList(Expression expr) {
      // The first element of each value's list in the result is the type of list
      Dictionary<string, List<string>> result = new Dictionary<string, List<string>>();
      HoleEvalGraph<string> G = new HoleEvalGraph<string>();
      foreach (var e in Expression.Conjuncts(expr)) {
        if (e is BinaryExpr && (e as BinaryExpr).ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon) {
          var be = e as BinaryExpr;
          var e0 = Printer.ExprToString(be.E0);
          var e1 = Printer.ExprToString(be.E1);
          if (e0 == e1) {
            continue;
          }
          if (!G.AdjacencyList.ContainsKey(e0)) {
            G.AddVertex(e0);
          }
          if (!G.AdjacencyList.ContainsKey(e1)) {
            G.AddVertex(e1);
          }
          G.AddEdge(new Tuple<string, string>(e0, e1));
        }
      }
      HashSet<string> visited = new HashSet<string>();
      foreach (var e in Expression.Conjuncts(expr)) {
        if (e is BinaryExpr && (e as BinaryExpr).ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon) {
          var be = e as BinaryExpr;
          var e0 = Printer.ExprToString(be.E0);
          var e1 = Printer.ExprToString(be.E1);
          if (e0 == e1) {
            continue;
          }
          if (visited.Contains(e0) || visited.Contains(e1)) {
            Debug.Assert(visited.Contains(e0));
            Debug.Assert(visited.Contains(e1));
            continue;
          }
          HashSet<string> newVisits = G.DFS(e0);
          visited.UnionWith(newVisits);
          result[e0] = new List<string>();
          // The first element of each value's list in the result is the type of list
          result[e0].Add(be.E0.Type.ToString());
          newVisits.Remove(e0);
          foreach (string s in newVisits) {
            result[e0].Add(s);
          }
        }
      }
      return result;
    }

    public static DirectedCallGraph<Function, FunctionCallExpr, Expression> GetCallGraph(Function baseFunc) {
      Contract.Requires(baseFunc != null);
      DirectedCallGraph<Function, FunctionCallExpr, Expression> G = new DirectedCallGraph<Function, FunctionCallExpr, Expression>();
      // Tuple of SubExpression that is going to be parsed, pre-condition to reach this SubExpression, containing Function
      Queue<Tuple<Expression, Expression, Function>> queue = new Queue<Tuple<Expression, Expression, Function>>();
      queue.Enqueue(new Tuple<Expression, Expression, Function>(baseFunc.Body, null, baseFunc));
      G.AddVertex(baseFunc);
      HashSet<string> seenFunctionCalls = new HashSet<string>();
      // keys.Add(Printer.ExprToString(baseF.Body) + ":" + baseF.Body);
      // TODO: Check an example in which a function is called in another function with two different pre-conditions
      while (queue.Count > 0) {
        Tuple<Expression, Expression, Function> currExprCondParentTuple = queue.Dequeue();
        if (currExprCondParentTuple.Item1 == null) continue;
        // Console.WriteLine("Processing " + currExprParentTuple.Item1 + ": " + Printer.ExprToString(currExprParentTuple.Item1));
        if (currExprCondParentTuple.Item1 is FunctionCallExpr /*&& (currExpr as FunctionCallExpr).Function.Body != null*/) {
          // if (!keys.Contains(Printer.ExprToString((currExprParentTuple.Item1 as FunctionCallExpr).Function.Body) + ":" + (currExprParentTuple.Item1 as FunctionCallExpr).Function.Body)) {
          // Console.WriteLine("Adding " + (currExprParentTuple.Item1 as FunctionCallExpr).Function.Body + ": " + Printer.ExprToString((currExprParentTuple.Item1 as FunctionCallExpr).Function.Body));
          var funcCallCondAsString = $"{currExprCondParentTuple.Item3.Name} -> " +
                                     $"{(currExprCondParentTuple.Item1 as FunctionCallExpr).Function.Name} -> ";
          if (currExprCondParentTuple.Item2 != null) {
            funcCallCondAsString += $"{Printer.ExprToString(currExprCondParentTuple.Item2)}";
          } else {
            funcCallCondAsString += "NULL";
          }
          if (!seenFunctionCalls.Contains(funcCallCondAsString)) {
            seenFunctionCalls.Add(funcCallCondAsString);
            // if (currExprCondParentTuple.Item2 != null) {
            //   Console.WriteLine($"condition : {Printer.ExprToString(currExprCondParentTuple.Item2)}");
            // } else {
            //   Console.WriteLine($"condition : null");
            // }
            queue.Enqueue(new Tuple<Expression, Expression, Function>(
              (currExprCondParentTuple.Item1 as FunctionCallExpr).Function.Body,
              null,
              (currExprCondParentTuple.Item1 as FunctionCallExpr).Function));
            G.AddVertex((currExprCondParentTuple.Item1 as FunctionCallExpr).Function);
            G.AddEdge(
              currExprCondParentTuple.Item3,
              (currExprCondParentTuple.Item1 as FunctionCallExpr).Function,
              currExprCondParentTuple.Item1 as FunctionCallExpr,
              currExprCondParentTuple.Item2);
            // Console.WriteLine("-------------------------------------");
            // keys.Add(Printer.ExprToString((currExprParentTuple.Item1 as FunctionCallExpr).Function.Body) + ":" + (currExprParentTuple.Item1 as FunctionCallExpr).Function.Body);
            // }
          }
        }
        if (currExprCondParentTuple.Item1 is ITEExpr) {
          // Console.WriteLine($"ite expr here: {Printer.ExprToString(currExprCondParentTuple.Item1)}");
          var iteExpr = currExprCondParentTuple.Item1 as ITEExpr;

          // add Condition
          queue.Enqueue(new Tuple<Expression, Expression, Function>(
            iteExpr.Test, currExprCondParentTuple.Item2, currExprCondParentTuple.Item3));

          // add then path
          var thenCond = currExprCondParentTuple.Item2 != null ?
            Expression.CreateAnd(currExprCondParentTuple.Item2, iteExpr.Test) :
            iteExpr.Test;
          queue.Enqueue(new Tuple<Expression, Expression, Function>(
            iteExpr.Thn, thenCond, currExprCondParentTuple.Item3));

          // add else path
          var elseCond = currExprCondParentTuple.Item2 != null ?
            Expression.CreateAnd(currExprCondParentTuple.Item2,
                                 Expression.CreateNot(iteExpr.Test.tok, iteExpr.Test)) :
            Expression.CreateNot(iteExpr.Test.tok, iteExpr.Test);
          queue.Enqueue(new Tuple<Expression, Expression, Function>(
            iteExpr.Els, elseCond, currExprCondParentTuple.Item3));

          G.AddVertex(currExprCondParentTuple.Item3);
        } else if (currExprCondParentTuple.Item1 is MatchExpr) {
          var matchExpr = currExprCondParentTuple.Item1 as MatchExpr;
          // add source
          queue.Enqueue(new Tuple<Expression, Expression, Function>(
            matchExpr.Source, currExprCondParentTuple.Item2, currExprCondParentTuple.Item3));

          // add cases
          // Console.WriteLine(Printer.ExprToString(matchExpr));
          foreach (var c in matchExpr.Cases) {
            // Console.WriteLine($"{c.Ctor} -> {c.Ctor.Name}");
            var cond = currExprCondParentTuple.Item2 != null ?
              Expression.CreateAnd(currExprCondParentTuple.Item2, new MemberSelectExpr(c.Ctor.tok, matchExpr.Source, c.Ctor.Name)) :
              new MemberSelectExpr(c.Ctor.tok, matchExpr.Source, c.Ctor.Name + "?");
            queue.Enqueue(new Tuple<Expression, Expression, Function>(
              c.Body, cond, currExprCondParentTuple.Item3));
          }
          G.AddVertex(currExprCondParentTuple.Item3);
          // Console.WriteLine("----------------------------------------------------------------");
        } else if (currExprCondParentTuple.Item1 is ExistsExpr) {
          var existsExpr = currExprCondParentTuple.Item1 as ExistsExpr;
          var lhss = new List<CasePattern<BoundVar>>();
          var rhss = new List<Expression>();
          foreach (var bv in existsExpr.BoundVars) {
            lhss.Add(new CasePattern<BoundVar>(bv.Tok,
              new BoundVar(bv.Tok, currExprCondParentTuple.Item3.Name + "_" + bv.Name, bv.Type)));
          }
          rhss.Add(existsExpr.Term);
          var cond = Expression.CreateLet(existsExpr.BodyStartTok, lhss, rhss,
            Expression.CreateBoolLiteral(existsExpr.BodyStartTok, true), false);

          queue.Enqueue(new Tuple<Expression, Expression, Function>(existsExpr.Term, cond, currExprCondParentTuple.Item3));
          G.AddVertex(currExprCondParentTuple.Item3);
        } else {
          foreach (var e in currExprCondParentTuple.Item1.SubExpressions) {
            // if (!keys.Contains(Printer.ExprToString(e) + ":" + e)) {
            // Console.WriteLine("Adding " + e + ": " + Printer.ExprToString(e));
            // if (e is MatchExpr) {
            //   // Console.WriteLine($"MatchExpr : {Printer.ExprToString(e)}");
            //   queue.Enqueue(new Tuple<Expression, Expression, Function>(e, e, currExprCondParentTuple.Item3));
            //   G.AddVertex(currExprCondParentTuple.Item3);
            // } else if (e is ITEExpr) {
            //   // Console.WriteLine($"ITEExpr : {Printer.ExprToString(e)}");
            //   queue.Enqueue(new Tuple<Expression, Expression, Function>(e, e, currExprCondParentTuple.Item3));
            //   G.AddVertex(currExprCondParentTuple.Item3);
            // } else {
            // Console.WriteLine($"else : {e} -> {Printer.ExprToString(e)}");
            queue.Enqueue(new Tuple<Expression, Expression, Function>(e, currExprCondParentTuple.Item2, currExprCondParentTuple.Item3));
            G.AddVertex(currExprCondParentTuple.Item3);
            // }
          }
        }
      }
      return G;
    }

    DirectedCallGraph<Function, FunctionCallExpr, Expression> CG;
    List<List<Tuple<Function, FunctionCallExpr, Expression>>> Paths =
      new List<List<Tuple<Function, FunctionCallExpr, Expression>>>();
    List<Tuple<Function, FunctionCallExpr, Expression>> CurrentPath =
      new List<Tuple<Function, FunctionCallExpr, Expression>>();

    public void GetAllPaths(Function source, Function destination) {
      if (source.FullDafnyName == destination.FullDafnyName) {
        Paths.Add(new List<Tuple<Function, FunctionCallExpr, Expression>>(CurrentPath));
        return;
      }
      foreach (var nwPair in CG.AdjacencyWeightList[source]) {
        CurrentPath.Add(new Tuple<Function, FunctionCallExpr, Expression>(
          nwPair.Item1, nwPair.Item2, nwPair.Item3));
        GetAllPaths(nwPair.Item1, destination);
        CurrentPath.RemoveAt(CurrentPath.Count - 1);
      }
    }

    public static string GetPrefixedString(string prefix, Expression expr, ModuleDefinition currentModuleDef) {
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr);
        pr.Prefix = prefix;
        pr.ModuleForTypes = currentModuleDef;
        pr.PrintExpression(expr, false);
        return wr.ToString();
      }
    }

    public static string GetNonPrefixedString(Expression expr, ModuleDefinition currentModuleDef) {
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr);
        pr.ModuleForTypes = currentModuleDef;
        pr.PrintExpression(expr, false);
        return wr.ToString();
      }
    }

   public static string GetBaseLemmaList(Function fn, ModuleDefinition currentModuleDef, Expression constraintExpr) {
      string res = "";
      // res += RemoveWhitespace(Printer.FunctionSignatureToString(fn));
      res += "\n{\n";
      res += Printer.ExprToString(fn.Body);
      res += "\n}";
      // return res;

        using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr);
        pr.ModuleForTypes = currentModuleDef;
        pr.PrintFunction(fn, 0,false);
        res = wr.ToString();
      }
      int i = res.IndexOf("(");
      String modStr1 = res.Insert(i, "_BASE");
      return modStr1;
    }

    public static string GetIsSameLemmaList(Function fn,List<Tuple<Function, FunctionCallExpr, Expression>> path, ModuleDefinition currentModuleDef, Expression constraintExpr,Boolean isQuantifier) {
      string res = "lemma isSame";
       foreach (var nwPair in path) {
        res += "_" + nwPair.Item1.Name;
      }
      res += "(";
      var sep = "";
      var p = "";
       Tuple<string, string> x = new Tuple<string, string>(null, null);
      foreach (var nwPair in path) {
        res += sep + " ";
        sep = "";
        x = GetFunctionParamList(nwPair.Item1);
        res += x.Item2;
        p += "" + x.Item1; 
        sep = ", ";
      }
      res += ")\n";
      foreach (var req in path[0].Item1.Req) {
       if(isQuantifier){
          res += "  requires forall " + x.Item2 + " :: "+ GetNonPrefixedString(req.E, currentModuleDef) + "\n";
        }else{
          res += "  requires " + GetNonPrefixedString(req.E, currentModuleDef) + "\n";
        }
      }
       if(p != ""){
        res += "  ensures forall " + p + " :: "+ fn.Name+ "("+p+") <==> " + fn.Name+"_BASE("+p+")\n{}";
       }else{
              res += "  ensures " + fn.Name+ "() <==> " + fn.Name+"_BASE()\n{}";

       }
      return res;
    }

    public static string GetIsStronger(Function fn,List<Tuple<Function, FunctionCallExpr, Expression>> path, ModuleDefinition currentModuleDef, Expression constraintExpr, Boolean isQuantifier) {
      string res = "lemma isStronger";
       foreach (var nwPair in path) {
        res += "_" + nwPair.Item1.Name;
      }
      res += "(";
      var sep = "";
      var p = "";
      Tuple<string, string> x = new Tuple<string, string>(null, null);

      foreach (var nwPair in path) {
        res += sep + " ";
        sep = "";
        x = GetFunctionParamList(nwPair.Item1);
        res += x.Item2;
        p += "" + x.Item1; 
        sep = ", ";
      }
      res += ")\n";
      foreach (var req in path[0].Item1.Req) {
        // Console.WriteLine("  requires forall " + x.Item2 + " :: "+ GetNonPrefixedString(req.E, currentModuleDef) + "\n");
        // res += "  requires " + GetPrefixedString(path[0].Item1.Name + "_", req.E, currentModuleDef) + "\n";
        if(isQuantifier){
          res += "  requires forall " + x.Item2 + " :: "+ GetNonPrefixedString(req.E, currentModuleDef) + "\n";
        }else{
          res += "  requires " + GetNonPrefixedString(req.E, currentModuleDef) + "\n";
        }
      }
      if(p != ""){
        res += "  ensures forall " + p + " :: "+ fn.Name+ "("+p+") ==> " + fn.Name+"_BASE("+p+")\n{}";
      }else{
        res += "  ensures " + fn.Name+ "() ==> " + fn.Name+"_BASE()\n{}";

      }
      return res;
    }

    public static string GetValidityLemma(List<Tuple<Function, FunctionCallExpr, Expression>> path, ModuleDefinition currentModuleDef, Expression constraintExpr) {
      string res = "lemma {:timeLimitMultiplier 2} validityCheck";
      foreach (var nwPair in path) {
        res += "_" + nwPair.Item1.Name;
      }
      res += "(";
      var sep = "";
      foreach (var nwPair in path) {
        res += sep + "\n    ";
        sep = "";
        res += GetFunctionParamList(nwPair.Item1, nwPair.Item1.Name + "_").Item2;
        sep = ", ";
      }
      res += ")\n";
      foreach (var req in path[0].Item1.Req) {
        res += "  requires " + GetPrefixedString(path[0].Item1.Name + "_", req.E, currentModuleDef) + "\n";
      }
      res += "  requires " + path[0].Item1.FullDafnyName + "(";
      sep = "";
      foreach (var formal in path[0].Item1.Formals) {
        res += sep + path[0].Item1.Name + "_" + formal.Name;
        sep = ", ";
      }
      res += ")\n";
      for (int i = 0; i < path.Count - 1; i++) {
        var callExpr = path[i + 1].Item2;
        var condExpr = path[i + 1].Item3;
        if (condExpr != null) {
          currentModuleDef = path[i].Item1.EnclosingClass.EnclosingModuleDefinition;
          res += "  requires " + GetPrefixedString(path[i].Item1.Name + "_", condExpr, currentModuleDef) + "\n";
        }
        for (int j = 0; j < callExpr.Args.Count; j++) {
          res += "  requires ";
          res += GetPrefixedString(path[i].Item1.Name + "_", callExpr.Args[j], currentModuleDef);
          res += " == ";
          res += path[i + 1].Item1.Name + "_" + path[i + 1].Item1.Formals[j].Name + "\n";
        }
        foreach (var req in callExpr.Function.Req) {
          res += "  requires " + GetPrefixedString(path[i + 1].Item1.Name + "_", req.E, currentModuleDef) + "\n";
        }
        res += "  requires " + callExpr.Function.FullDafnyName + "(";
        sep = "";
        foreach (var arg in callExpr.Args) {
          res += sep + GetPrefixedString(path[i].Item1.Name + "_", arg, currentModuleDef);
          sep = ", ";
        }
        res += ")\n";
      }
      if (constraintExpr != null) {
        currentModuleDef = path[0].Item1.EnclosingClass.EnclosingModuleDefinition;
        res += "  requires " + GetPrefixedString(path[0].Item1.Name + "_", constraintExpr, currentModuleDef) + "\n";
      }
      res += "  ensures false\n{}";
      return res;
    }

    public async Task<bool> EvaluateAfterRemoveFileLine(Program program, Program unresolvedProgram, string removeFileLine, string baseFuncName, int depth) {
      var fileLineArray = removeFileLine.Split(':');
      var file = fileLineArray[0];
      var line = Int32.Parse(fileLineArray[1]);
      foreach (var kvp in program.ModuleSigs) {
        foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
          if (Path.GetFileName(topLevelDecl.tok.filename) == file) {
            if (topLevelDecl.BodyStartTok.line <= line && line <= topLevelDecl.BodyEndTok.line) {
              var exprList = Expression.Conjuncts(topLevelDecl.Body).ToList();
              // Console.WriteLine($"topLevelDecl : {topLevelDecl.FullDafnyName}");
              var i = -1;
              for (i = 0; i < exprList.Count - 1; i++) {
                if (exprList[i].tok.line <= line && line < exprList[i + 1].tok.line) {
                  break;
                }
              }
              // Console.WriteLine($"{i} {Printer.ExprToString(exprList[i])}");
              exprList.RemoveAt(i);
              var body = exprList[0];
              for (int j = 1; j < exprList.Count; j++) {
                body = Expression.CreateAnd(body, exprList[j]);
              }
              topLevelDecl.Body = body;
              return await Evaluate(program, unresolvedProgram, topLevelDecl.FullDafnyName, baseFuncName, depth);
            }
          }
        }
      }
      return false;
    }

    public void PrintAllLemmas(Program program, string lemmaName) {
      foreach (var kvp in program.ModuleSigs) {
        foreach (var d in kvp.Value.ModuleDef.TopLevelDecls) {
          var cl = d as TopLevelDeclWithMembers;
          if (cl != null) {
            foreach (var member in cl.Members) {
              var m = member as Lemma;
              if (m != null) {
                Console.WriteLine("LEMMA NAME = " + m.FullDafnyName);
              }
            }
          }
        }
      }
    }
    public static Lemma GetLemma(Program program, string lemmaName) {
      foreach (var kvp in program.ModuleSigs) {
        foreach (var d in kvp.Value.ModuleDef.TopLevelDecls) {
          var cl = d as TopLevelDeclWithMembers;
          if (cl != null) {
            foreach (var member in cl.Members) {
              var m = member as Lemma;
              if (m != null) {
                if (m.FullDafnyName == lemmaName) {
                  return m;
                }
              }
            }
          }
        }
      }
      return null;
    }
public async Task<bool> EvaluateFilterStrongerAndSame(Program program, Program unresolvedProgram, string funcName, string lemmaName, string proofModuleName, string baseFuncName, int depth) {
      if(proofModuleName != null)
      {
        // Console.WriteLine("MOUDLE = " + proofModuleName);
      }
      if (DafnyOptions.O.HoleEvaluatorServerIpPortList == null) {
        Console.WriteLine("ip port list is not given. Please specify with /holeEvalServerIpPortList");
        return false;
      }
      if (DafnyOptions.O.HoleEvaluatorCommands != null) {
        var input = File.ReadAllText(DafnyOptions.O.HoleEvaluatorCommands);
        tasksList = Google.Protobuf.JsonParser.Default.Parse<TasksList>(input);
      }
      dafnyVerifier = new DafnyVerifierClient(DafnyOptions.O.HoleEvaluatorServerIpPortList, $"output_{funcName}");
      expressionFinder = new ExpressionFinder(this);
      bool runOnce = DafnyOptions.O.HoleEvaluatorRunOnce;
      int timeLimitMultiplier = 2;
      int timeLimitMultiplierLength = 0;
      while (timeLimitMultiplier >= 1) {
        timeLimitMultiplierLength++;
        timeLimitMultiplier /= 10;
      }
      validityLemmaNameStartCol = 30 + timeLimitMultiplierLength;

      // Collect all paths from baseFunc to func
      Console.WriteLine($"{funcName} {baseFuncName} {depth}");
      if (baseFuncName == null) {
        baseFuncName = funcName;
      }
      Function baseFunc = GetFunction(program, baseFuncName);


      if (baseFunc == null) {
        Console.WriteLine($"couldn't find function {baseFuncName}. List of all functions:");
        foreach (var kvp in program.ModuleSigs) {
          foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
            Console.WriteLine(topLevelDecl.FullDafnyName);
          }
        }
        return false;
      }
      Lemma baseLemma = GetLemma(program, lemmaName);
      if (baseLemma == null) {
        Console.WriteLine($"couldn't find function {lemmaName}. List of all lemmas:");
        PrintAllLemmas(program, lemmaName);
        return false;
      }

      Function constraintFunc = null;
      if (DafnyOptions.O.HoleEvaluatorConstraint != null) {
        constraintFunc = GetFunction(program, DafnyOptions.O.HoleEvaluatorConstraint);
        if (constraintFunc == null) {
          Console.WriteLine($"constraint function {DafnyOptions.O.HoleEvaluatorConstraint} not found!");
          return false;
        }
      }
      CG = GetCallGraph(baseFunc);
      Function func = GetFunction(program, funcName);
      CurrentPath.Add(new Tuple<Function, FunctionCallExpr, Expression>(baseFunc, null, null));
      GetAllPaths(baseFunc, func);
      if (Paths.Count == 0)
        Paths.Add(new List<Tuple<Function, FunctionCallExpr, Expression>>(CurrentPath));
      // foreach (var p in Paths) {
      //   Console.WriteLine(GetValidityLemma(p));
      //   Console.WriteLine("\n----------------------------------------------------------------\n");
      // }
      // return true;

      UnderscoreStr = RandomString(8);
      dafnyVerifier.sw = Stopwatch.StartNew();
      Console.WriteLine($"hole evaluation begins for func {funcName}");
      Function desiredFunction = null;
      Function desiredFunctionUnresolved = null;
      Function topLevelDeclCopy = null;
      desiredFunction = GetFunction(program, funcName);
      // Console.WriteLine("--Function to Mutate--");
      // using (var wr = new System.IO.StringWriter()) {
      //   var pr = new Printer(wr);
      //   pr.PrintFunction(desiredFunction, 0,false);
      //   Console.WriteLine(wr.ToString());
      // }
      // Console.WriteLine("--------------");

      if (desiredFunction != null) {
        includeParser = new IncludeParser(program);
        var filename = includeParser.Normalized(desiredFunction.BodyStartTok.Filename);
        foreach (var file in includeParser.GetListOfAffectedFilesBy(filename)) {
          affectedFiles.Add(file);
        }
        // calculate holeEvaluatorConstraint Invocation
        if (constraintFunc != null) {
          Dictionary<string, List<Expression>> typeToExpressionDictForInputs = new Dictionary<string, List<Expression>>();
          foreach (var formal in baseFunc.Formals) {
            var identExpr = Expression.CreateIdentExpr(formal);
            var typeString = formal.Type.ToString();
            if (typeToExpressionDictForInputs.ContainsKey(typeString)) {
              typeToExpressionDictForInputs[typeString].Add(identExpr);
            } else {
              var lst = new List<Expression>();
              lst.Add(identExpr);
              typeToExpressionDictForInputs.Add(typeString, lst);
            }
          }
          var funcCalls = ExpressionFinder.GetAllPossibleFunctionInvocations(program, constraintFunc, typeToExpressionDictForInputs);
          foreach (var funcCall in funcCalls) {
            if (constraintExpr == null) {
              constraintExpr = funcCall;
            } else {
              constraintExpr = Expression.CreateAnd(constraintExpr, funcCall);
            }
          }
          Console.WriteLine($"constraint expr to be added : {Printer.ExprToString(constraintExpr)}");
        }
        expressionFinder.CalcDepthOneAvailableExpresssionsFromFunctionBody(program, desiredFunction);
        // Console.WriteLine(GetBaseLemmaList(baseFunc, null, constraintExpr));
        // expressionFinder.CalcDepthOneAvailableExpresssionsFromFunction(program, desiredFunction);
        desiredFunctionUnresolved = GetFunctionFromUnresolvedClass(unresolvedProgram, funcName);
        // Console.WriteLine("BEFORE");
        if(desiredFunctionUnresolved == null){
          desiredFunctionUnresolved = GetFunction(program, funcName);
        }
      //         Console.WriteLine("--Function to Mutate--");
      // using (var wr = new System.IO.StringWriter()) {
      //   var pr = new Printer(wr);
      //   pr.PrintFunction(desiredFunction, 0,false);
      //   Console.WriteLine(wr.ToString());
      // }
      // Console.WriteLine("--------------");
        Contract.Assert(desiredFunctionUnresolved != null);
        
        // Console.WriteLine("AFTER");
        topLevelDeclCopy = new Function(
          desiredFunctionUnresolved.tok, desiredFunctionUnresolved.Name, desiredFunctionUnresolved.HasStaticKeyword,
          desiredFunctionUnresolved.IsGhost, desiredFunctionUnresolved.TypeArgs, desiredFunctionUnresolved.Formals,
          desiredFunctionUnresolved.Result, desiredFunctionUnresolved.ResultType, desiredFunctionUnresolved.Req,
          desiredFunctionUnresolved.Reads, desiredFunctionUnresolved.Ens, desiredFunctionUnresolved.Decreases,
          desiredFunctionUnresolved.Body, desiredFunctionUnresolved.ByMethodTok, desiredFunctionUnresolved.ByMethodBody,
          desiredFunctionUnresolved.Attributes, desiredFunctionUnresolved.SignatureEllipsis);
      } else {
        Console.WriteLine($"{funcName} was not found!");
        return false;
      }
      Console.WriteLine($"expressionFinder.availableExpressions.Count == {expressionFinder.availableExpressions.Count}");
      // Console.WriteLine(expressionFinder.availableExpressions);
      for (int i = 0; i < expressionFinder.availableExpressions.Count; i++) {
      // for (int i = 0; i < 1; i++) {
        desiredFunctionUnresolved.Body = topLevelDeclCopy.Body;

        PrintExprAndCreateProcessLemma(unresolvedProgram, desiredFunctionUnresolved, baseLemma,proofModuleName,expressionFinder.availableExpressions[i], i,false,false);
        await dafnyVerifier.startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs();

     var isStronger = isDafnyVerifySuccessful(i);
      if(isStronger){
        Console.WriteLine("Passed Stronger Test on (" + i + ")! Trying isSame");
        desiredFunctionUnresolved.Body = topLevelDeclCopy.Body;

        PrintExprAndCreateProcessLemma(unresolvedProgram, desiredFunctionUnresolved, baseLemma,proofModuleName,expressionFinder.availableExpressions[i], i,false,true);
        await dafnyVerifier.startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs();
        var isSame = isDafnyVerifySuccessful(i);
        desiredFunctionUnresolved.Body = topLevelDeclCopy.Body;

        if(!isSame){
          Console.WriteLine("Passed Stronger Test AND Same Test on (" + i + ")! Trying Full Proof");
          PrintExprAndCreateProcessLemma(unresolvedProgram, desiredFunctionUnresolved,baseLemma,proofModuleName,expressionFinder.availableExpressions[i], i,true,false);
        }else{
          var request = dafnyVerifier.requestsList[i];
          dafnyVerifier.dafnyOutput[request].Response = "isSame";
        }
      }
      }
      await dafnyVerifier.startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs();
      Console.WriteLine("finish");

      // bool foundCorrectExpr = false;
      for (int i = 0; i < expressionFinder.availableExpressions.Count; i++) {
        UpdateCombinationResult(i);
        // foundCorrectExpr |= combinationResults[i] == Result.CorrectProof;
      }

      // Until here, we only check depth 1 of expressions.
      // Now we try to check next depths
      // int numberOfSingleExpr = expressionFinder.availableExpressions.Count;
      // for (int dd = 2; dd <= depth; dd++) {
      //   var prevDepthExprStartIndex = expressionFinder.availableExpressions.Count;
      //   expressionFinder.CalcNextDepthAvailableExpressions();
      //   for (int i = prevDepthExprStartIndex; i < expressionFinder.availableExpressions.Count; i++) {
      //     var expr = expressionFinder.availableExpressions[i];
      //     PrintExprAndCreateProcess(program, desiredFunction, expr, i);
      //     desiredFunction.Body = topLevelDeclCopy.Body;
      //   }
      //   await dafnyVerifier.startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs();
      //   for (int i = prevDepthExprStartIndex; i < expressionFinder.availableExpressions.Count; i++) {
      //     UpdateCombinationResult(i);
      //   }
      // }
      Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: finish exploring, try to calculate implies graph");
      int correctProofCount = 0;
      int correctProofByTimeoutCount = 0;
      int incorrectProofCount = 0;
      int invalidExprCount = 0;
      int falsePredicateCount = 0;
      int noMatchingTriggerCount = 0;
      for (int i = 0; i < expressionFinder.availableExpressions.Count; i++) {
        switch (combinationResults[i]) {
          case Result.InvalidExpr: invalidExprCount++; break;
          case Result.FalsePredicate: falsePredicateCount++; break;
          case Result.CorrectProof: correctProofCount++; break;
          case Result.CorrectProofByTimeout: correctProofByTimeoutCount++; break;
          case Result.IncorrectProof: incorrectProofCount++; break;
          case Result.NoMatchingTrigger: noMatchingTriggerCount++; break;
          case Result.Unknown: throw new NotSupportedException();
        }
      }
      // Console.WriteLine("{0,-15} {1,-15} {2,-15} {3,-15} {4, -25} {5, -15} {6, -15}",
      //   "InvalidExpr", "IncorrectProof", "FalsePredicate", "CorrectProof", "CorrectProofByTimeout", "NoMatchingTrigger", "Total");
      // Console.WriteLine("{0,-15} {1,-15} {2,-15} {3,-15} {4, -25} {5, -15} {6, -15}",
      //   invalidExprCount, incorrectProofCount, falsePredicateCount, correctProofCount, correctProofByTimeoutCount,
      //   noMatchingTriggerCount, expressionFinder.availableExpressions.Count);
      Console.WriteLine("{0,-15} {1,-15} {2,-15} {3,-15}",
        "InvalidExpr", "IncorrectProof", "ProofPasses", "Total");
      Console.WriteLine("{0,-15} {1,-15} {2,-15} {3,-15}",
        invalidExprCount, incorrectProofCount, falsePredicateCount, expressionFinder.availableExpressions.Count);
      string executionTimesSummary = "";
      // executionTimes.Sort();
      for (int i = 0; i < executionTimes.Count; i++) {
        executionTimesSummary += $"{i}, {executionTimes[i].ToString()}\n";
      }
      await File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}/executionTimeSummary.txt",
            executionTimesSummary);

      string startTimesSummary = "";
      // startTimes.Sort();
      for (int i = 0; i < startTimes.Count; i++) {
        startTimesSummary += $"{i}, {(startTimes[i] - startTimes[0]).ToString()}\n";
      }
      await File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}/startTimeSummary.txt",
            startTimesSummary);
      // for (int i = 0; i < bitArrayList.Count; i++) {
      //   var ba = bitArrayList[i];
      //   Console.WriteLine("------------------------------");
      //   Console.WriteLine(i + " : " +
      //                     Printer.ExprToString(availableExpressions[i]) + " : " +
      //                     combinationResults[i].ToString());
      //   Console.WriteLine(ToBitString(ba));
      //   Console.WriteLine("------------------------------");
      // }
      // return true;

      // int correctExpressionCount = combinationResults.Count(elem => elem.Value == Result.CorrectProof);
      // if (correctExpressionCount == 0) {
      //   Console.WriteLine("Couldn't find any correct answer. Printing 0 error ones");
      //   for (int i = 0; i < availableExpressions.Count; i++) {
      //     if (combinationResults[i] == Result.InvalidExpr) {
      //       var p = dafnyMainExecutor.dafnyProcesses[i];
      //       Console.WriteLine(p.StartInfo.Arguments);
      //       Console.WriteLine(Printer.ExprToString(dafnyMainExecutor.processToExpr[p]));
      //     }
      //   }
      //   return false;
      // }
      // The 0th process represents no change to the predicate, and
      // if that is a correct predicate, it means the proof already 
      // goes through and no additional conjunction is needed.
      if (combinationResults[0] == Result.CorrectProof || combinationResults[0] == Result.CorrectProofByTimeout) {
        Console.WriteLine("proof already goes through and no additional conjunction is needed!");
        return true;
      }
      return true;
      List<int> correctExpressionsIndex = new List<int>();
      for (int i = 0; i < expressionFinder.availableExpressions.Count; i++) {
        if (combinationResults[i] == Result.CorrectProof || combinationResults[i] == Result.CorrectProofByTimeout)
          correctExpressionsIndex.Add(i);
      }
      // for (int i = 0; i < correctExpressionsIndex.Count; i++) {
      //   Console.WriteLine($"correct Expr #{correctExpressionsIndex[i],3}: {Printer.ExprToString(availableExpressions[correctExpressionsIndex[i]])}");
      // }
      for (int i = 0; i < correctExpressionsIndex.Count; i++) {
        for (int j = i + 1; j < correctExpressionsIndex.Count; j++) {
          {
            PrintImplies(program, desiredFunction, correctExpressionsIndex[i], correctExpressionsIndex[j]);
            PrintImplies(program, desiredFunction, correctExpressionsIndex[j], correctExpressionsIndex[i]);
          }
        }
      }
      dafnyImpliesExecutor.startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs(true);
      Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: finish calculating implies, printing the dot graph");
      string graphVizOutput = $"digraph \"{funcName}_implies_graph\" {{\n";
      graphVizOutput += "  // The list of correct expressions\n";
      for (int i = 0; i < correctExpressionsIndex.Count; i++) {
        graphVizOutput += $"  {correctExpressionsIndex[i]} [label=\"{Printer.ExprToString(expressionFinder.availableExpressions[correctExpressionsIndex[i]])}\"];\n";
      }
      graphVizOutput += "\n  // The list of edges:\n";
      foreach (var p in dafnyImpliesExecutor.dafnyProcesses) {
        var availableExprAIndex = dafnyImpliesExecutor.processToAvailableExprAIndex[p];
        var availableExprBIndex = dafnyImpliesExecutor.processToAvailableExprBIndex[p];
        // skip connecting all nodes to true
        if (Printer.ExprToString(expressionFinder.availableExpressions[availableExprAIndex]) == "true" ||
            Printer.ExprToString(expressionFinder.availableExpressions[availableExprBIndex]) == "true")
          continue;
        var output = dafnyImpliesExecutor.dafnyOutput[p];
        if (output.EndsWith("0 errors\n")) {
          Console.WriteLine($"edge from {availableExprAIndex} to {availableExprBIndex}");
          graphVizOutput += $"  {availableExprAIndex} -> {availableExprBIndex};\n";
        }
      }
      graphVizOutput += "}\n";
      await File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}graph_{funcName}_implies.dot", graphVizOutput);
      Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: end");
      return true;
    }


  public Boolean isDafnyVerifySuccessful(int i)
  {
    var request = dafnyVerifier.requestsList[i];
      var position = dafnyVerifier.requestToPostConditionPosition[request];
      var lemmaStartPosition = dafnyVerifier.requestToLemmaStartPosition[request];
      var output = dafnyVerifier.dafnyOutput[request];
      var response = output.Response;
      var filePath = output.FileName;
      var startTime = output.StartTime;
      var execTime = output.ExecutionTime;
      executionTimes.Add(execTime);
      startTimes.Add(startTime);
      var expectedOutput =
        $"{filePath}({position},0): Error: A postcondition might not hold on this return path.";
      var expectedInconclusiveOutputStart =
        $"{filePath}({lemmaStartPosition},{validityLemmaNameStartCol}): Verification inconclusive";
      var res = DafnyVerifierClient.IsCorrectOutput(response, expectedOutput, expectedInconclusiveOutputStart);
      return response.EndsWith("0 errors\n");
  }







    public async Task<bool> Evaluate(Program program, Program unresolvedProgram, string funcName, string baseFuncName, int depth) {
      if (DafnyOptions.O.HoleEvaluatorServerIpPortList == null) {
        Console.WriteLine("ip port list is not given. Please specify with /holeEvalServerIpPortList");
        return false;
      }
      if (DafnyOptions.O.HoleEvaluatorCommands != null) {
        var input = File.ReadAllText(DafnyOptions.O.HoleEvaluatorCommands);
        tasksList = Google.Protobuf.JsonParser.Default.Parse<TasksList>(input);
      }
      dafnyVerifier = new DafnyVerifierClient(DafnyOptions.O.HoleEvaluatorServerIpPortList, $"output_{funcName}");
      expressionFinder = new ExpressionFinder(this);
      bool runOnce = DafnyOptions.O.HoleEvaluatorRunOnce;
      int timeLimitMultiplier = 2;
      int timeLimitMultiplierLength = 0;
      while (timeLimitMultiplier >= 1) {
        timeLimitMultiplierLength++;
        timeLimitMultiplier /= 10;
      }
      validityLemmaNameStartCol = 30 + timeLimitMultiplierLength;

      // Collect all paths from baseFunc to func
      Console.WriteLine($"{funcName} {baseFuncName} {depth}");
      if (baseFuncName == null) {
        baseFuncName = funcName;
      }
      Function baseFunc = GetFunction(program, baseFuncName);
      if (baseFunc == null) {
        Console.WriteLine($"couldn't find function {baseFuncName}. List of all functions:");
        foreach (var kvp in program.ModuleSigs) {
          foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
            Console.WriteLine(topLevelDecl.FullDafnyName);
          }
        }
        return false;
      }
      Function constraintFunc = null;
      if (DafnyOptions.O.HoleEvaluatorConstraint != null) {
        constraintFunc = GetFunction(program, DafnyOptions.O.HoleEvaluatorConstraint);
        if (constraintFunc == null) {
          Console.WriteLine($"constraint function {DafnyOptions.O.HoleEvaluatorConstraint} not found!");
          return false;
        }
      }
      CG = GetCallGraph(baseFunc);
      Function func = GetFunction(program, funcName);
      CurrentPath.Add(new Tuple<Function, FunctionCallExpr, Expression>(baseFunc, null, null));
      GetAllPaths(baseFunc, func);
      if (Paths.Count == 0)
        Paths.Add(new List<Tuple<Function, FunctionCallExpr, Expression>>(CurrentPath));
      // foreach (var p in Paths) {
      //   Console.WriteLine(GetValidityLemma(p));
      //   Console.WriteLine("\n----------------------------------------------------------------\n");
      // }
      // return true;

      UnderscoreStr = RandomString(8);
      dafnyVerifier.sw = Stopwatch.StartNew();
      Console.WriteLine($"hole evaluation begins for func {funcName}");
      Function desiredFunction = null;
      Function desiredFunctionUnresolved = null;
      Function topLevelDeclCopy = null;
      desiredFunction = GetFunction(program, funcName);
      if (desiredFunction != null) {
        includeParser = new IncludeParser(program);
        var filename = includeParser.Normalized(desiredFunction.BodyStartTok.Filename);
        foreach (var file in includeParser.GetListOfAffectedFilesBy(filename)) {
          affectedFiles.Add(file);
        }
        // calculate holeEvaluatorConstraint Invocation
        if (constraintFunc != null) {
          Dictionary<string, List<Expression>> typeToExpressionDictForInputs = new Dictionary<string, List<Expression>>();
          foreach (var formal in baseFunc.Formals) {
            var identExpr = Expression.CreateIdentExpr(formal);
            var typeString = formal.Type.ToString();
            if (typeToExpressionDictForInputs.ContainsKey(typeString)) {
              typeToExpressionDictForInputs[typeString].Add(identExpr);
            } else {
              var lst = new List<Expression>();
              lst.Add(identExpr);
              typeToExpressionDictForInputs.Add(typeString, lst);
            }
          }
          var funcCalls = ExpressionFinder.GetAllPossibleFunctionInvocations(program, constraintFunc, typeToExpressionDictForInputs);
          foreach (var funcCall in funcCalls) {
            if (constraintExpr == null) {
              constraintExpr = funcCall;
            } else {
              constraintExpr = Expression.CreateAnd(constraintExpr, funcCall);
            }
          }
          Console.WriteLine($"constraint expr to be added : {Printer.ExprToString(constraintExpr)}");
        }
        expressionFinder.CalcDepthOneAvailableExpresssionsFromFunctionBody(program, desiredFunction);
        // Console.WriteLine(GetBaseLemmaList(baseFunc, null, constraintExpr));
        // expressionFinder.CalcDepthOneAvailableExpresssionsFromFunction(program, desiredFunction);
        desiredFunctionUnresolved = GetFunctionFromUnresolved(unresolvedProgram, funcName);
        if(desiredFunctionUnresolved == null){
          desiredFunctionUnresolved = desiredFunction;
        }
        Contract.Assert(desiredFunctionUnresolved != null);
        topLevelDeclCopy = new Function(
          desiredFunctionUnresolved.tok, desiredFunctionUnresolved.Name, desiredFunctionUnresolved.HasStaticKeyword,
          desiredFunctionUnresolved.IsGhost, desiredFunctionUnresolved.TypeArgs, desiredFunctionUnresolved.Formals,
          desiredFunctionUnresolved.Result, desiredFunctionUnresolved.ResultType, desiredFunctionUnresolved.Req,
          desiredFunctionUnresolved.Reads, desiredFunctionUnresolved.Ens, desiredFunctionUnresolved.Decreases,
          desiredFunctionUnresolved.Body, desiredFunctionUnresolved.ByMethodTok, desiredFunctionUnresolved.ByMethodBody,
          desiredFunctionUnresolved.Attributes, desiredFunctionUnresolved.SignatureEllipsis);
      } else {
        Console.WriteLine($"{funcName} was not found!");
        return false;
      }
      Console.WriteLine($"expressionFinder.availableExpressions.Count == {expressionFinder.availableExpressions.Count}");
      // Console.WriteLine(expressionFinder.availableExpressions);
      for (int i = 0; i < expressionFinder.availableExpressions.Count; i++) {
      // for (int i = 0; i < 1; i++) {
        PrintExprAndCreateProcess(unresolvedProgram, desiredFunctionUnresolved, expressionFinder.availableExpressions[i], i);
        desiredFunctionUnresolved.Body = topLevelDeclCopy.Body;
                 await dafnyVerifier.startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs();

      // Console.WriteLine("lengeth = " + dafnyVerifier.requestsList.Count + " :: " + i);
      var request = dafnyVerifier.requestsList[i];
      var position = dafnyVerifier.requestToPostConditionPosition[request];
      var lemmaStartPosition = dafnyVerifier.requestToLemmaStartPosition[request];
      var output = dafnyVerifier.dafnyOutput[request];
      var response = output.Response;
      var filePath = output.FileName;
      var startTime = output.StartTime;
      var execTime = output.ExecutionTime;
      executionTimes.Add(execTime);
      startTimes.Add(startTime);
      var expectedOutput =
        $"{filePath}({position},0): Error: A postcondition might not hold on this return path.";
      var expectedInconclusiveOutputStart =
        $"{filePath}({lemmaStartPosition},{validityLemmaNameStartCol}): Verification inconclusive";
      // Console.WriteLine($"{index} => {output}");
      // Console.WriteLine($"{output.EndsWith("0 errors\n")} {output.EndsWith($"resolution/type errors detected in {fileName}.dfy\n")}");
      // Console.WriteLine($"----------------------------------------------------------------");
      var res = DafnyVerifierClient.IsCorrectOutput(response, expectedOutput, expectedInconclusiveOutputStart);
      if(response.EndsWith("0 errors\n")){
        Console.WriteLine("Passed!");
      }
      // Console.WriteLine("HERE " + res + " " + response + ":: " + response.EndsWith("0 errors\n"));
        // Console.WriteLine("HERE + " + (topLevelDeclCopy.ToString()));
      }
      await dafnyVerifier.startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs();
      Console.WriteLine("finish");

      // bool foundCorrectExpr = false;
      for (int i = 0; i < expressionFinder.availableExpressions.Count; i++) {
        UpdateCombinationResult(i);
        // foundCorrectExpr |= combinationResults[i] == Result.CorrectProof;
      }

      // Until here, we only check depth 1 of expressions.
      // Now we try to check next depths
      int numberOfSingleExpr = expressionFinder.availableExpressions.Count;
      for (int dd = 2; dd <= depth; dd++) {
        var prevDepthExprStartIndex = expressionFinder.availableExpressions.Count;
        expressionFinder.CalcNextDepthAvailableExpressions();
        for (int i = prevDepthExprStartIndex; i < expressionFinder.availableExpressions.Count; i++) {
          var expr = expressionFinder.availableExpressions[i];
          PrintExprAndCreateProcess(program, desiredFunction, expr, i);
          desiredFunction.Body = topLevelDeclCopy.Body;
        }
        await dafnyVerifier.startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs();
        for (int i = prevDepthExprStartIndex; i < expressionFinder.availableExpressions.Count; i++) {
          UpdateCombinationResult(i);
        }
      }
      Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: finish exploring, try to calculate implies graph");
      int correctProofCount = 0;
      int correctProofByTimeoutCount = 0;
      int incorrectProofCount = 0;
      int invalidExprCount = 0;
      int falsePredicateCount = 0;
      int noMatchingTriggerCount = 0;
      for (int i = 0; i < expressionFinder.availableExpressions.Count; i++) {
        switch (combinationResults[i]) {
          case Result.InvalidExpr: invalidExprCount++; break;
          case Result.FalsePredicate: falsePredicateCount++; break;
          case Result.CorrectProof: correctProofCount++; break;
          case Result.CorrectProofByTimeout: correctProofByTimeoutCount++; break;
          case Result.IncorrectProof: incorrectProofCount++; break;
          case Result.NoMatchingTrigger: noMatchingTriggerCount++; break;
          case Result.Unknown: throw new NotSupportedException();
        }
      }
      // Console.WriteLine("{0,-15} {1,-15} {2,-15} {3,-15} {4, -25} {5, -15} {6, -15}",
      //   "InvalidExpr", "IncorrectProof", "FalsePredicate", "CorrectProof", "CorrectProofByTimeout", "NoMatchingTrigger", "Total");
      // Console.WriteLine("{0,-15} {1,-15} {2,-15} {3,-15} {4, -25} {5, -15} {6, -15}",
      //   invalidExprCount, incorrectProofCount, falsePredicateCount, correctProofCount, correctProofByTimeoutCount,
      //   noMatchingTriggerCount, expressionFinder.availableExpressions.Count);
      Console.WriteLine("{0,-15} {1,-15} {2,-15} {3,-15}",
        "InvalidExpr", "IncorrectProof", "ProofPasses", "Total");
      Console.WriteLine("{0,-15} {1,-15} {2,-15} {3,-15}",
        invalidExprCount, incorrectProofCount, falsePredicateCount, expressionFinder.availableExpressions.Count);
      string executionTimesSummary = "";
      // executionTimes.Sort();
      for (int i = 0; i < executionTimes.Count; i++) {
        executionTimesSummary += $"{i}, {executionTimes[i].ToString()}\n";
      }
      await File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}/executionTimeSummary.txt",
            executionTimesSummary);

      string startTimesSummary = "";
      // startTimes.Sort();
      for (int i = 0; i < startTimes.Count; i++) {
        startTimesSummary += $"{i}, {(startTimes[i] - startTimes[0]).ToString()}\n";
      }
      await File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}/startTimeSummary.txt",
            startTimesSummary);
      // for (int i = 0; i < bitArrayList.Count; i++) {
      //   var ba = bitArrayList[i];
      //   Console.WriteLine("------------------------------");
      //   Console.WriteLine(i + " : " +
      //                     Printer.ExprToString(availableExpressions[i]) + " : " +
      //                     combinationResults[i].ToString());
      //   Console.WriteLine(ToBitString(ba));
      //   Console.WriteLine("------------------------------");
      // }
      // return true;

      // int correctExpressionCount = combinationResults.Count(elem => elem.Value == Result.CorrectProof);
      // if (correctExpressionCount == 0) {
      //   Console.WriteLine("Couldn't find any correct answer. Printing 0 error ones");
      //   for (int i = 0; i < availableExpressions.Count; i++) {
      //     if (combinationResults[i] == Result.InvalidExpr) {
      //       var p = dafnyMainExecutor.dafnyProcesses[i];
      //       Console.WriteLine(p.StartInfo.Arguments);
      //       Console.WriteLine(Printer.ExprToString(dafnyMainExecutor.processToExpr[p]));
      //     }
      //   }
      //   return false;
      // }
      // The 0th process represents no change to the predicate, and
      // if that is a correct predicate, it means the proof already 
      // goes through and no additional conjunction is needed.
      if (combinationResults[0] == Result.CorrectProof || combinationResults[0] == Result.CorrectProofByTimeout) {
        Console.WriteLine("proof already goes through and no additional conjunction is needed!");
        return true;
      }
      return true;
      List<int> correctExpressionsIndex = new List<int>();
      for (int i = 0; i < expressionFinder.availableExpressions.Count; i++) {
        if (combinationResults[i] == Result.CorrectProof || combinationResults[i] == Result.CorrectProofByTimeout)
          correctExpressionsIndex.Add(i);
      }
      // for (int i = 0; i < correctExpressionsIndex.Count; i++) {
      //   Console.WriteLine($"correct Expr #{correctExpressionsIndex[i],3}: {Printer.ExprToString(availableExpressions[correctExpressionsIndex[i]])}");
      // }
      for (int i = 0; i < correctExpressionsIndex.Count; i++) {
        for (int j = i + 1; j < correctExpressionsIndex.Count; j++) {
          {
            PrintImplies(program, desiredFunction, correctExpressionsIndex[i], correctExpressionsIndex[j]);
            PrintImplies(program, desiredFunction, correctExpressionsIndex[j], correctExpressionsIndex[i]);
          }
        }
      }
      dafnyImpliesExecutor.startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs(true);
      Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: finish calculating implies, printing the dot graph");
      string graphVizOutput = $"digraph \"{funcName}_implies_graph\" {{\n";
      graphVizOutput += "  // The list of correct expressions\n";
      for (int i = 0; i < correctExpressionsIndex.Count; i++) {
        graphVizOutput += $"  {correctExpressionsIndex[i]} [label=\"{Printer.ExprToString(expressionFinder.availableExpressions[correctExpressionsIndex[i]])}\"];\n";
      }
      graphVizOutput += "\n  // The list of edges:\n";
      foreach (var p in dafnyImpliesExecutor.dafnyProcesses) {
        var availableExprAIndex = dafnyImpliesExecutor.processToAvailableExprAIndex[p];
        var availableExprBIndex = dafnyImpliesExecutor.processToAvailableExprBIndex[p];
        // skip connecting all nodes to true
        if (Printer.ExprToString(expressionFinder.availableExpressions[availableExprAIndex]) == "true" ||
            Printer.ExprToString(expressionFinder.availableExpressions[availableExprBIndex]) == "true")
          continue;
        var output = dafnyImpliesExecutor.dafnyOutput[p];
        if (output.EndsWith("0 errors\n")) {
          Console.WriteLine($"edge from {availableExprAIndex} to {availableExprBIndex}");
          graphVizOutput += $"  {availableExprAIndex} -> {availableExprBIndex};\n";
        }
      }
      graphVizOutput += "}\n";
      await File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}graph_{funcName}_implies.dot", graphVizOutput);
      Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: end");
      return true;
    }

    public static string GetFullModuleName(ModuleDefinition moduleDef) {
      if (moduleDef.Name == "_module") {
        return "";
      } else if (moduleDef.EnclosingModule.Name == "_module") {
        return moduleDef.Name;
      } else {
        return GetFullModuleName(moduleDef.EnclosingModule) + "." + moduleDef.Name;
      }
    }

    public static string GetFullLemmaNameString(ModuleDefinition moduleDef, string name) {
      if (moduleDef is null) {
        return name;
      }
      foreach (var decl in ModuleDefinition.AllFunctions(moduleDef.TopLevelDecls)) {
        if (decl.ToString() == name) {
          var moduleName = GetFullModuleName(moduleDef);
          return (moduleName == "") ? name : (moduleName + "." + name);
        }
      }
      foreach (var imp in ModuleDefinition.AllDeclarationsAndNonNullTypeDecls(moduleDef.TopLevelDecls)) {
        if (imp is ModuleDecl) {
          var result = GetFullLemmaNameString((imp as ModuleDecl).Signature.ModuleDef, name);
          if (result != "") {
            return result;
          }
        }
      }
      // couldn't find the type definition here, so we should search the parent
      return "";
    }

    public static string GetFullTypeString(ModuleDefinition moduleDef, Type type) {
      if (moduleDef is null) {
        return type.ToString();
      }
      if (type is UserDefinedType) {
        var udt = type as UserDefinedType;
        if (udt.Name == "nat" || udt.Name == "object?")
          return udt.ToString();
        foreach (var decl in moduleDef.TopLevelDecls) {
          if (decl.ToString() == type.ToString()) {
            var moduleName = GetFullModuleName(moduleDef);
            return (moduleName == "") ? type.ToString() : (moduleName + "." + type.ToString());
          }
        }
        if (moduleDef.Name != "_module") {
          foreach (var imp in ModuleDefinition.AllDeclarationsAndNonNullTypeDecls(moduleDef.TopLevelDecls)) {
            if (imp is ModuleDecl) {
              var result = GetFullTypeString((imp as ModuleDecl).Signature.ModuleDef, type);
              if (result != "") {
                return result;
              }
            }
          }
        }
        // couldn't find the type definition here, so we should search the parent
        if (moduleDef.EnclosingModule != moduleDef) {
          return GetFullTypeString(moduleDef.EnclosingModule, type);
        } else {
          return type.ToString();
        }
      } else if (type is CollectionType) {
        var ct = type as CollectionType;
        var result = ct.CollectionTypeName + "<";
        var sep = "";
        foreach (var typeArg in ct.TypeArgs) {
          result += sep + GetFullTypeString(moduleDef, typeArg);
          sep = ",";
        }
        result += ">";
        return result;
      } else {
        return type.ToString();
      }
    }

    public static Tuple<string, string> GetFunctionParamList(Function func, string namePrefix = "") {
      var funcName = func.FullDafnyName;
      string parameterNameTypes = "";
      string paramNames = "";
      var sep = "";
      foreach (var param in func.Formals) {
        // parameterNameTypes += sep + namePrefix + param.Name + ":" + GetFullTypeString(func.EnclosingClass.EnclosingModuleDefinition, param.Type);
        parameterNameTypes += sep + namePrefix + param.Name + ":" + GetFullTypeString(null, param.Type);
        paramNames += sep + namePrefix + param.Name;
        sep = ", ";
      }
      return new Tuple<string, string>(paramNames, parameterNameTypes);
    }

    public static Function GetFunction(Program program, string funcName) {
      foreach (var kvp in program.ModuleSigs) {
        foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
          if (topLevelDecl.FullDafnyName == funcName) {
            return topLevelDecl;
          }
        }
      }
      return null;
    }

    public static Function GetFunctionFromModuleDef(ModuleDefinition moduleDef, string funcName) {
      foreach (var topLevelDecl in moduleDef.TopLevelDecls) {
        if (topLevelDecl is ClassDecl) {
          var cd = topLevelDecl as ClassDecl;
          foreach (var member in cd.Members) {
            // Console.WriteLine($"{cd.FullDafnyName}.{member.Name}");
            if ($"{cd.FullDafnyName}.{member.Name}" == funcName) {
              return member as Function;
            }
          }
        }
      }
      return null;
    }

    public static Function GetFunctionFromUnresolved(Program program, string funcName) {
      int index = funcName.LastIndexOf('.');
      string moduleName = funcName.Remove(index);
      foreach (var topLevelDecl in program.DefaultModuleDef.TopLevelDecls) {
        if(topLevelDecl.FullDafnyName == moduleName) {
          var lmd = topLevelDecl as LiteralModuleDecl;
          var func = GetFunctionFromModuleDef(lmd.ModuleDef, funcName);
          if (func != null) {
            return func;
          }
        }
      }
      return null;
    }

    public static Function GetFunctionFromUnresolvedClass(Program program, string funcName) {
      int index = funcName.IndexOf('.');
      string moduleName = funcName.Remove(index);
      foreach (var topLevelDecl in program.DefaultModuleDef.TopLevelDecls) {
        if(topLevelDecl.FullDafnyName == moduleName) {
          var lmd = topLevelDecl as LiteralModuleDecl;
          var func = GetFunctionFromModuleDef(lmd.ModuleDef, funcName);
          if (func != null) {
            return func;
          }
        }
      }
      return null;
    }

    public void DuplicateAllFiles(Program program, string workingDir, int cnt)
    {
      if (System.IO.Directory.Exists(workingDir))
      {
        System.IO.Directory.Delete(workingDir, true);
      }
      System.IO.Directory.CreateDirectory(workingDir);
      var samples = new List<string>();
      samples.Add(includeParser.Normalized(program.FullName));
      System.IO.Directory.CreateDirectory(Path.GetDirectoryName($"{workingDir}/{samples[0]}"));
      File.Copy(program.FullName, $"{workingDir}/{samples[0]}", true);
      foreach (var file in program.DefaultModuleDef.Includes) {
        samples.Add(includeParser.Normalized(file.CanonicalPath));
      }
      for (int i = 1; i < samples.Count; i++) {
        System.IO.Directory.CreateDirectory(Path.GetDirectoryName($"{workingDir}/{samples[i]}"));
        File.Copy(program.DefaultModuleDef.Includes[i - 1].CanonicalPath, $"{workingDir}/{samples[i]}", true);
      }
    }

    public void PrintExprAndCreateProcess(Program program, Function func, Expression expr, int cnt) {
      bool runOnce = DafnyOptions.O.HoleEvaluatorRunOnce;
      Console.WriteLine("Mutation -> " + $"{cnt}" + ": " + $"{Printer.ExprToString(expr)}");
      var funcName = func.Name;

      string lemmaForExprValidityString = ""; // remove validityCheck
      string basePredicateString = GetBaseLemmaList(func,null, constraintExpr);
      string isSameLemma = GetIsSameLemmaList(func,Paths[0], null, constraintExpr,false);
      string isStrongerLemma = GetIsStronger(func,Paths[0], null, constraintExpr,false);
      // Console.WriteLine(isSameLemma);
      int lemmaForExprValidityPosition = 0;
      int lemmaForExprValidityStartPosition = 0;
      int basePredicatePosition = 0;
      int basePredicateStartPosition = 0;
      var workingDir = $"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}/{funcName}_{cnt}";
      if (tasksList == null)
      {
        string code = "";
        using (var wr = new System.IO.StringWriter()) {
          var pr = new Printer(wr, DafnyOptions.PrintModes.DllEmbed);
          pr.UniqueStringBeforeUnderscore = UnderscoreStr;
          // if (expr.HasCardinality) {
          //   func.Body = Expression.CreateAnd(expr, func.Body);
          // } else {
          //   func.Body = Expression.CreateAnd(func.Body, expr);
          // }
          func.Body = expr; // Replace Whole Body
          pr.PrintProgram(program, true);
          code = $"// #{cnt}\n";
          code += $"// {Printer.ExprToString(expr)}\n" + Printer.ToStringWithoutNewline(wr) + "\n\n";
          
          int fnIndex = code.IndexOf("predicate " + funcName);
          code = code.Insert(fnIndex-1,basePredicateString+"\n");

          // fnIndex = code.IndexOf("predicate " + funcName);
          // code = code.Insert(fnIndex-1,isSameLemma+"\n");
          
          fnIndex = code.IndexOf("predicate " + funcName);
          code = code.Insert(fnIndex-1,isStrongerLemma+"\n");
          // lemmaForExprValidityStartPosition = code.Count(f => f == '\n') + 1;
          // code += lemmaForExprValidityString + "\n";
          // lemmaForExprValidityPosition = code.Count(f => f == '\n');

          // basePredicateStartPosition = code.Count(f => f == '\n') + 1;
          // code += basePredicateString + "\n";
          // basePredicatePosition = code.Count(f => f == '\n');

          // Console.WriteLine(code.IndexOf("lemma isSame_"+funcName));
          if (DafnyOptions.O.HoleEvaluatorCreateAuxFiles)
            File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{funcName}_{cnt}.dfy", code);
        }
        string env = DafnyOptions.O.Environment.Remove(0, 22);
        var argList = env.Split(' ');
        List<string> args = new List<string>();
        foreach (var arg in argList) {
          if (!arg.EndsWith(".dfy") && !arg.StartsWith("/holeEval") && arg.StartsWith("/")) {
            args.Add(arg);
          }
        }
        // args.Add("/exitAfterFirstError");
        dafnyVerifier.runDafny(code, args,
            expr, cnt, lemmaForExprValidityPosition, lemmaForExprValidityStartPosition);
       
      }
      else
      {
        DuplicateAllFiles(program, workingDir, cnt);

        Expression newFuncBody = null;
        if (expr.HasCardinality) {
          newFuncBody = Expression.CreateAnd(expr, func.Body);
        } else {
          newFuncBody = Expression.CreateAnd(func.Body, expr);
        }
        var baseCode = File.ReadAllLines(func.BodyStartTok.Filename);
        if (func.BodyStartTok.line == func.BodyEndTok.line) {
          baseCode[func.BodyStartTok.line - 1] = baseCode[func.BodyStartTok.line - 1].Remove(func.BodyStartTok.col, func.BodyEndTok.col - func.BodyStartTok.col);
          baseCode[func.BodyStartTok.line - 1] = baseCode[func.BodyStartTok.line - 1].Insert(func.BodyStartTok.col + 1, Printer.ExprToString(newFuncBody));
        }
        else {
          baseCode[func.BodyStartTok.line - 1] = baseCode[func.BodyStartTok.line - 1].Remove(func.BodyStartTok.col);
          for (int i = func.BodyStartTok.line; i < func.BodyEndTok.line - 1; i++) {
            baseCode[i] = "";
          }
          baseCode[func.BodyEndTok.line - 1] = baseCode[func.BodyEndTok.line - 1].Remove(0, func.BodyEndTok.col - 1);
          baseCode[func.BodyStartTok.line - 1] = baseCode[func.BodyStartTok.line - 1].Insert(func.BodyStartTok.col, Printer.ExprToString(newFuncBody));
        }
        lemmaForExprValidityStartPosition = baseCode.Length;
        baseCode = baseCode.Append(lemmaForExprValidityString).ToArray();
        lemmaForExprValidityPosition = baseCode.Length;
        var newCode = String.Join('\n', baseCode);
        File.WriteAllTextAsync($"{workingDir}/{includeParser.Normalized(func.BodyStartTok.Filename)}", newCode);
      }
    }

    public void PrintExprAndCreateProcessLemma(Program program, Function func, Lemma lemma,string moduleName,Expression expr, int cnt, bool includeProof, bool isSame) {
      bool runOnce = DafnyOptions.O.HoleEvaluatorRunOnce;
      Console.WriteLine("Mutation -> " + $"{cnt}" + ": " + $"{Printer.ExprToString(expr)}");
      var funcName = func.Name;

      string lemmaForExprValidityString = ""; // remove validityCheck
      string basePredicateString = GetBaseLemmaList(func,null, constraintExpr);
      string isSameLemma = "";
      string isStrongerLemma = "";

      if(expr is QuantifierExpr){
        isStrongerLemma = GetIsStronger(func,Paths[0], null, constraintExpr,true);
        isSameLemma = GetIsSameLemmaList(func,Paths[0], null, constraintExpr,true);
      }else{
        isStrongerLemma = GetIsStronger(func,Paths[0], null, constraintExpr,false);
        isSameLemma = GetIsSameLemmaList(func,Paths[0], null, constraintExpr,false);
      }

      int lemmaForExprValidityPosition = 0;
      int lemmaForExprValidityStartPosition = 0;
      int basePredicatePosition = 0;
      int basePredicateStartPosition = 0;
      var workingDir = $"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}/{funcName}_{cnt}";
      if (tasksList == null)
      {
        string code = "";
        using (var wr = new System.IO.StringWriter()) {
          var pr = new Printer(wr, DafnyOptions.PrintModes.DllEmbed);
          pr.UniqueStringBeforeUnderscore = UnderscoreStr;
          // if (expr.HasCardinality) {
          //   func.Body = Expression.CreateAnd(expr, func.Body);
          // } else {
          //   func.Body = Expression.CreateAnd(func.Body, expr);
          // }
          func.Body = expr; // Replace Whole Body
          // lemma.Body = new Block;
      //     Console.WriteLine("--Function is Mutated--");
      // using (var wr1 = new System.IO.StringWriter()) {
      //   var pr1 = new Printer(wr);
      //   pr1.PrintFunction(func, 0,false);
      //   Console.WriteLine(wr1.ToString());
      // }
      // Console.WriteLine("--------------");
          pr.PrintProgram(program, true);
          code = $"// #{cnt}\n";
          code += $"// {Printer.ExprToString(expr)}\n" + Printer.ToStringWithoutNewline(wr) + "\n\n";
          
          int fnIndex = code.IndexOf("predicate " + funcName);
          code = code.Insert(fnIndex-1,basePredicateString+"\n");
          if(!includeProof){
            if(moduleName != null){
              // comment out entire module "assume this is last module"! 
              int moduleLoc = code.IndexOf("module " +moduleName);
              code = code.Insert(moduleLoc-1,"/*"+"\n");
              code = code + "/*";
            }else{
              //Comment out single 'proof' lemma
              int lemmaLoc = code.IndexOf("lemma " +lemma.Name);
              code = code.Insert(lemmaLoc-1,"/*"+"\n");
              code = code.Insert(code.IndexOf("}\n\n",lemmaLoc)-1,"*/"+"\n");
            }
          }

          if(isSame){
            fnIndex = code.IndexOf("predicate " + funcName);
            code = code.Insert(fnIndex-1,isSameLemma+"\n");
          }
          
          fnIndex = code.IndexOf("predicate " + funcName);
          code = code.Insert(fnIndex-1,isStrongerLemma+"\n");


          // lemmaForExprValidityStartPosition = code.Count(f => f == '\n') + 1;
          // code += lemmaForExprValidityString + "\n";
          // lemmaForExprValidityPosition = code.Count(f => f == '\n');

          // basePredicateStartPosition = code.Count(f => f == '\n') + 1;
          // code += basePredicateString + "\n";
          // basePredicatePosition = code.Count(f => f == '\n');

          // Console.WriteLine(code.IndexOf("lemma isSame_"+funcName));
          if (DafnyOptions.O.HoleEvaluatorCreateAuxFiles)
            File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{funcName}_{cnt}.dfy", code);
        }
        string env = DafnyOptions.O.Environment.Remove(0, 22);
        var argList = env.Split(' ');
        List<string> args = new List<string>();
        foreach (var arg in argList) {
          if (!arg.EndsWith(".dfy") && !arg.StartsWith("/holeEval") && arg.StartsWith("/")) {
            args.Add(arg);
          }
        }
        // args.Add("/exitAfterFirstError");
        dafnyVerifier.runDafny(code, args,
            expr, cnt, lemmaForExprValidityPosition, lemmaForExprValidityStartPosition);
       
      }
      else
      {
        DuplicateAllFiles(program, workingDir, cnt);

        Expression newFuncBody = null;
        if (expr.HasCardinality) {
          newFuncBody = Expression.CreateAnd(expr, func.Body);
        } else {
          newFuncBody = Expression.CreateAnd(func.Body, expr);
        }
        var baseCode = File.ReadAllLines(func.BodyStartTok.Filename);
        if (func.BodyStartTok.line == func.BodyEndTok.line) {
          baseCode[func.BodyStartTok.line - 1] = baseCode[func.BodyStartTok.line - 1].Remove(func.BodyStartTok.col, func.BodyEndTok.col - func.BodyStartTok.col);
          baseCode[func.BodyStartTok.line - 1] = baseCode[func.BodyStartTok.line - 1].Insert(func.BodyStartTok.col + 1, Printer.ExprToString(newFuncBody));
        }
        else {
          baseCode[func.BodyStartTok.line - 1] = baseCode[func.BodyStartTok.line - 1].Remove(func.BodyStartTok.col);
          for (int i = func.BodyStartTok.line; i < func.BodyEndTok.line - 1; i++) {
            baseCode[i] = "";
          }
          baseCode[func.BodyEndTok.line - 1] = baseCode[func.BodyEndTok.line - 1].Remove(0, func.BodyEndTok.col - 1);
          baseCode[func.BodyStartTok.line - 1] = baseCode[func.BodyStartTok.line - 1].Insert(func.BodyStartTok.col, Printer.ExprToString(newFuncBody));
        }
        lemmaForExprValidityStartPosition = baseCode.Length;
        baseCode = baseCode.Append(lemmaForExprValidityString).ToArray();
        lemmaForExprValidityPosition = baseCode.Length;
        var newCode = String.Join('\n', baseCode);
        File.WriteAllTextAsync($"{workingDir}/{includeParser.Normalized(func.BodyStartTok.Filename)}", newCode);
      }
    }

    public void PrintImplies(Program program, Function func, int availableExprAIndex, int availableExprBIndex) {
      // Console.WriteLine($"print implies {availableExprAIndex} {availableExprBIndex}");
      var funcName = func.FullDafnyName;
      var paramList = GetFunctionParamList(func);
      var parameterNameTypes = paramList.Item2;
      string lemmaForCheckingImpliesString = "lemma checkIfExprAImpliesExprB(";
      lemmaForCheckingImpliesString += parameterNameTypes + ")\n";
      Expression A = expressionFinder.availableExpressions[availableExprAIndex];
      Expression B = expressionFinder.availableExpressions[availableExprBIndex];
      lemmaForCheckingImpliesString += "  requires " + Printer.ExprToString(A) + "\n";
      lemmaForCheckingImpliesString += "  ensures " + Printer.ExprToString(B) + "\n";
      lemmaForCheckingImpliesString += "{}";

      int lemmaForCheckingImpliesPosition = 0;

      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr, DafnyOptions.PrintModes.DllEmbed);
        pr.UniqueStringBeforeUnderscore = UnderscoreStr;
        pr.PrintProgram(program, true);
        var code = $"// Implies {Printer.ExprToString(A)} ==> {Printer.ExprToString(B)}\n" + Printer.ToStringWithoutNewline(wr) + "\n\n";
        code += lemmaForCheckingImpliesString + "\n";
        lemmaForCheckingImpliesPosition = code.Count(f => f == '\n');
        File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{funcName}_implies_{availableExprAIndex}_{availableExprBIndex}.dfy", code);
      }

      string dafnyBinaryPath = System.Reflection.Assembly.GetEntryAssembly().Location;
      dafnyBinaryPath = dafnyBinaryPath.Substring(0, dafnyBinaryPath.Length - 4);
      string env = DafnyOptions.O.Environment.Remove(0, 22);
      var argList = env.Split(' ');
      string args = "";
      foreach (var arg in argList) {
        if (!arg.EndsWith(".dfy") && !arg.StartsWith("/holeEval") && !arg.StartsWith("/proc:") && args.StartsWith("/")) {
          args += arg + " ";
        }
      }
      dafnyImpliesExecutor.createProcessWithOutput(dafnyBinaryPath,
        $"{args} {DafnyOptions.O.HoleEvaluatorWorkingDirectory}{funcName}_implies_{availableExprAIndex}_{availableExprBIndex}.dfy /proc:Impl*checkIfExprAImpliesExprB*",
        availableExprAIndex, availableExprBIndex, -1, lemmaForCheckingImpliesPosition,
        $"{funcName}_implies_{availableExprAIndex}_{availableExprBIndex}.dfy");
    }

  }
}
