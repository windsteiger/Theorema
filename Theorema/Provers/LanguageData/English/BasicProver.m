
(* ::Section:: *)
(* Public Declaration Part: executes in Theorema`Provers` *)

With[ {lang = "English"},

MessageName[ basicProver, "usage", lang] = "The prover that handles the basic language constructs from the Theorema language, standard propositional and predicate logic.";
MessageName[ quantifierRules, "usage", lang] = "The prover that handles quantifiers.";
MessageName[ applyOnce, "usage", lang] = "applyOnce[ rules, prfsit] applies a matching inference rule from rules to the proof situation prfsit once.";
MessageName[ trySeveral, "usage", lang] = "trySeveral[ rules, prfsit] tries several rules from rules to the proof situation prfsit at the same time.";

] (* With *)


(* ::Section:: *)
(* Private Implementation Part: executes in Theorema`Provers`Private` *)

Begin["`Private`"]

With[ {lang = "English"},

translate[ "Quantifier Rules", lang] = "Quantifier Rules";
translate[ "Basic Prover", lang] = "Basic Prover";
translate[ "connectives", lang] = "Logical connectives";
translate[ "equality", lang] = "Logical equality";

proofStepText[ "andGoal", lang, used_, generated_, ___] := {textCell[ "For proving ", referenceCell[ First[ used]], " we prove the individual conjuncts."]};

subProofHeader[ "andGoal", lang, used_, generated_, {p_}] := {textCell[ "Proof of ", referenceCell[ Part[ generated, p]], ":"],
	textCell[ "We need to prove "],
	goalCell[ Part[ generated, p], "."]
	};

] (* With *)

End[]