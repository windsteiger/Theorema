BeginPackage["Theorema`Computation`Language`"]

(*
   Load the same symbols like in Theorema`Language` so that all language constructs will be
   available in Computation context as well *)

Needs[ "Theorema`Common`"]
   
Map[ Get, FileNames[ "*.m", ToFileName[{$TheoremaDirectory, "Theorema", "Language", "LanguageData"}]]];

Begin[ "`Private`"]

activeComputationKB[_] := False

buiActive[ f_String] :=
	Switch[ $computationContext,
		"prove",
		buiActProve[ f], 
		"compute",
		buiActComputation[ f],
		"solve",
		buiActSolve[ f]
	]
buiActive[ args___] := unexpected[ buiActive, {args}]

setComputationContext[ c_String] :=
    Module[ {},
        $computationContext = c;
    ]
setComputationContext[ args___] := unexpected[ setComputationContext, {args}]

   
Plus$TM /; buiActive["Plus"] = Plus
Times$TM /; buiActive["Times"] = Times
Equal$TM /; buiActive["Equal"] = equal$TC
Forall$TM /; buiActive["Forall"] = forall$TC
Exists$TM /; buiActive["Exists"] = exists$TC

End[]
EndPackage[]