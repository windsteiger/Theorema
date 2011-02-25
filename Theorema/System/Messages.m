(* Mathematica Package *)

BeginPackage["Theorema`System`Messages`", {"Theorema`"}]
(* Exported symbols added here with SymbolName::usage *)  

Map[ Get, FileNames[ "*.m", ToFileName[{$TheoremaDirectory, "Theorema", "System", "LanguageData"}]]];

Begin["`Private`"] (* Begin Private Context *) 

unexpected[f_, args_List] := 
	Module[{}, 
		Message[ Theorema::unexpectedArgs, f, args];
		Throw[f]
	]
	
End[] (* End Private Context *)

EndPackage[]