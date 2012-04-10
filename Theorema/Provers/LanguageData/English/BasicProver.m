
(* ::Section:: *)
(* Public Declaration Part: executes in Theorema`Provers` *)

With[ {lang = "English"},

MessageName[ basicProver, "usage", lang] = "Rules for the basic language constructs from the Theorema language, standard propositional and predicate logic.";
MessageName[ quantifierRules, "usage", lang] = "Rules for quantifiers.";

MessageName[ andGoal, "usage", lang] = "Split a conjunction in the goal into several subgoals.";
MessageName[ implGoalDirect, "usage", lang] = "Prove implication directly.";
MessageName[ implGoalCP, "usage", lang] = "Prove implication using contraposition.";

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
	textCell[ "We need to prove"],
	goalCell[ Part[ generated, p], "."]
	};

proofStepText[ "implGoalDirect", lang, used_, generated_, ___] := {textCell[ "In order to prove ", referenceCell[ First[ used]], " we assume"],
	assumptionCell[ First[ generated]],
	textCell[ "and then prove"],
	goalCell[ generated[[2]], "."]
	};

proofStepText[ "implGoalCP", lang, used_, generated_, ___] := {textCell[ "We prove ", referenceCell[ First[ used]], " by contraposition, i.e. we assume"],
	assumptionCell[ First[ generated]],
	textCell[ "and prove"],
	goalCell[ generated[[2]], "."]
	};


] (* With *)

End[]