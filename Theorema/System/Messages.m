(* Mathematica Package *)

BeginPackage["Theorema`System`Messages`"]
(* Exported symbols added here with SymbolName::usage *)  

Needs["Theorema`Common`"]

Begin["`Private`"] (* Begin Private Context *) 

unexpected[f_, args_List] := 
	Module[{}, 
		Message[ Theorema::unexpectedArgs, f, args];
		Throw[f]
	]
	
End[] (* End Private Context *)

EndPackage[]