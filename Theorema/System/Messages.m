(* Mathematica Package *)

BeginPackage["Theorema`System`Messages`", {"Theorema`"}]
(* Exported symbols added here with SymbolName::usage *)  

Theorema::unexpectedArgs = "Function `1` called with unexpected arguments `2`.";

unexpected::usage = "unexpected[ f, {args}] terminates the evaluation of f[args] due to unexpected arguments.";

Begin["`Private`"] (* Begin Private Context *) 

unexpected[f_, args_List] := 
	Module[{}, 
		Message[ Theorema::unexpectedArgs, f, args];
		Throw[f]
	]
	
End[] (* End Private Context *)

EndPackage[]