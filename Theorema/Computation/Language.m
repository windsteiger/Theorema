BeginPackage["Theorema`Computation`Language`", {"Theorema`"}]

(*
   Load the same symbols like in Theorema`Language` so that all language constructs will be
   available in Computation context as well *)
   
Map[ Get, FileNames[ "*.m", ToFileName[{$TheoremaDirectory, "Theorema", "Language", "LanguageData"}]]];

Begin[ "`Private`"]

activeComputationKB[_] := False

(* TODO:
   Make activeComputation check a global parameter that tells whether computation is done inside a proof or
   on the global level. GUI can then set activeComputation or activeProof resp., and active[x] (instead
   of activeComputation) can then
   check the appropriate one with the help of the global setting *)
   
Plus$TM /; activeComputation["Plus"] = Plus
Times$TM /; activeComputation["Times"] = Times
Equal$TM /; activeComputation["Equal"] = equal$TC
Forall$TM /; activeComputation["Forall"] = forall$TC
Exists$TM /; activeComputation["Exists"] = exists$TC

End[]
EndPackage[]