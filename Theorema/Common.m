(* Mathematica Package *)

BeginPackage["Theorema`Common`", {"Theorema`"}]
(* Exported symbols added here with SymbolName::usage *)  

(*
  The sole task of this package is to export symbols that other packages want to share
*)

Map[ Get, FileNames[ "*.m", ToFileName[{$TheoremaDirectory, "Theorema", "System", "LanguageData"}]]];

EndPackage[]