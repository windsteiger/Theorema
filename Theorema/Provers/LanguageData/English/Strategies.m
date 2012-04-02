
(* ::Section:: *)
(* Public Declaration Part: executes in Theorema`Provers` *)

With[ {lang = "English"},

MessageName[ applyOnce, "usage", lang] = "applyOnce[ rules, prfsit] applies a matching inference rule from rules to the proof situation prfsit once.";
MessageName[ trySeveral, "usage", lang] = "trySeveral[ rules, prfsit] tries several rules from rules to the proof situation prfsit at the same time.";

] (* With *)


(* ::Section:: *)
(* Private Implementation Part: executes in Theorema`Provers`Private` *)

Begin["`Private`"]

With[ {lang = "English"},

translate[ "Apply once", lang] = "Apply once";
translate[ "Try several", lang] = "Try several";

] (* With *)

End[]