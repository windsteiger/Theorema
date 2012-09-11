
(* ::Section:: *)
(* Public Declaration Part: executes in Theorema`Provers` *)

With[ {lang = "English"},

MessageName[ basicTheoremaLanguageRules, "usage", lang] = "Rules for the basic language constructs from the Theorema language, standard propositional and predicate logic.";
MessageName[ quantifierRules, "usage", lang] = "Rules for quantifiers.";

MessageName[ notGoal, "usage", lang] = "Prove negation by contradiction.";
MessageName[ andGoal, "usage", lang] = "Split a conjunction in the goal.";
MessageName[ andKB, "usage", lang] = "Split a conjunction in the knowledge base.";
MessageName[ orGoal, "usage", lang] = "Handle a disjunction in the goal.";
MessageName[ orKB, "usage", lang] = "Case distinction based on a disjunction in the knowledge base.";
MessageName[ implGoalDirect, "usage", lang] = "Prove implication directly.";
MessageName[ implGoalCP, "usage", lang] = "Prove implication using contraposition.";
MessageName[ equivGoal, "usage", lang] = "Prove equivalence by double implication.";
MessageName[ contradiction, "usage", lang] = "Prove by contradiction.";

] (* With *)


(* ::Section:: *)
(* Private Implementation Part: executes in Theorema`Provers`Private` *)

Begin["`Private`"]

With[ {lang = "English"},

translate[ "Quantifier Rules", lang] = "Quantifier Rules";
translate[ "Basic Theorema Language Rules", lang] = "Basic Theorema Language Rules";
translate[ "Connectives Rules", lang] = "Rules for Logical Connectives";
translate[ "Equality Rules", lang] = "Rules for Equality";

proofStepText[ notGoal|contradiction, lang, {g_}, {opp_, ___}, ___] := {textCell[ "We prove ", formulaReference[ g], " by contradiction, i.e. we assume"],
	assumptionCell[ opp],
	textCell[ "and derive a contradiction."]
	};

proofStepText[ andGoal, lang, {g_}, generated_, ___] := {textCell[ "For proving ", formulaReference[ g], " we prove the individual conjuncts."]};

subProofHeader[ andGoal, lang, used_List, generated_List, pVal_, {p_}] := {textCell[ "Proof of ", formulaReference[ Part[ generated, p]], ":"],
	textCell[ "We need to prove"],
	goalCell[ Part[ generated, p], "."]
	};

proofStepText[ andKB, lang, {g_}, generated_, ___] := {textCell[ "We split the conjunction ", formulaReference[ g], " and add"],
	assumptionListCells[ generated, ",", ""],
	textCell[ "to the knowledge base."]
	};

proofStepText[ orGoal, lang, {g_}, {negAssum__, newG_}, ___] := {textCell[ "For proving the disjunction", formulaReference[ g], " we assume"],
	assumptionListCells[ {negAssum}, ",", ""],
	textCell[ "and show"],
	goalCell[ newG, "."]
};

proofStepText[ orKB, lang, {g_}, generated_, ___] := {textCell[ "Based on the assumption ", formulaReference[ g], " we distinguish several cases:"]};

subProofHeader[ orKB, lang, used_List, generated_List, pVal_, {p_}] := {textCell[ "Case ", ToString[p], ": we assume"],
	assumptionCell[ Part[ generated, p], "."]
	};

proofStepText[ implGoalDirect, lang, {g_}, {l_, r_}, ___] := {textCell[ "In order to prove ", formulaReference[ g], " we assume"],
	assumptionCell[ l],
	textCell[ "and then prove"],
	goalCell[ r, "."]
	};

proofStepText[ implGoalCP, lang, {g_}, {nr_, nl_}, ___] := {textCell[ "We prove ", formulaReference[ g], " by contraposition, i.e. we assume"],
	assumptionCell[ nr],
	textCell[ "and prove"],
	goalCell[ nl, "."]
	};


] (* With *)

End[]