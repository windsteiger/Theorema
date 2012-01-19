BeginPackage["Theorema`Computation`"]

activeComputation[_] := False
activeComputationKB[_] := False

Plus$TM /; activeComputation["Plus"] = Plus
Times$TM /; activeComputation["Times"] = Times
Set$TM /; activeComputation["Equal"] = equal$TC
Forall$TM /; activeComputation["Forall"] = forall$TC
Exists$TM /; activeComputation["Exists"] = exists$TC

EndPackage[]