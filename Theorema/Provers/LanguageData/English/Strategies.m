
(* ::Section:: *)
(* Public Declaration Part: executes in Theorema`Provers` *)

With[ {lang = "English"},

MessageName[ applyOnce, "usage", lang] = "applyOnce[ prfsit] applies a matching inference rule from rules to the proof situation prfsit once.";
MessageName[ applyOnceAndLevelSaturation, "usage", lang] = "applyOnceAndLevelSaturation[ prfsit] applies a matching inference rule to the proof situation prfsit once and then applies level saturation techniques.";
MessageName[ trySeveral, "usage", lang] = "trySeveral[ prfsit] tries several rules from rules to the proof situation prfsit at the same time.";

] (* With *)


(* ::Section:: *)
(* Private Implementation Part: executes in Theorema`Provers`Private` *)

Begin["`Private`"]

With[ {lang = "English"},

translate[ "Apply once", lang] = "Apply once";
translate[ "Apply once + Level saturation", lang] = "Apply once + Level saturation";
translate[ "Try several", lang] = "Try several";

] (* With *)

End[]