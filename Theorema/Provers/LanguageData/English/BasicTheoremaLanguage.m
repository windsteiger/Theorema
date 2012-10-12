
(* ::Section:: *)
(* Public Declaration Part: executes in Theorema`Provers` *)

With[ {lang = "English"},

MessageName[ basicTheoremaLanguageRules, "usage", lang] = "Rules for the basic language constructs from the Theorema language, standard propositional and predicate logic";
MessageName[ quantifierRules, "usage", lang] = "Rules for quantifiers";

MessageName[ contradictionKB, "usage", lang] = "Knowledge base contains contradicting formulae";
MessageName[ falseInKB, "usage", lang] = "Knowledge base contains a formula False";
MessageName[ goalInKB, "usage", lang] = "Knowledge base contains the proof goal";
MessageName[ trueGoal, "usage", lang] = "The proof goal is True";
MessageName[ notGoal, "usage", lang] = "Prove negation by contradiction";
MessageName[ andGoal, "usage", lang] = "Split a conjunction in the goal";
MessageName[ andKB, "usage", lang] = "Split a conjunction in the knowledge base";
MessageName[ orGoal, "usage", lang] = "Handle a disjunction in the goal";
MessageName[ orKB, "usage", lang] = "Case distinction based on a disjunction in the knowledge base";
MessageName[ implGoalDirect, "usage", lang] = "Prove implication directly";
MessageName[ implGoalCP, "usage", lang] = "Prove implication using contraposition";
MessageName[ equivGoal, "usage", lang] = "Prove equivalence by double implication";
MessageName[ contradiction, "usage", lang] = "Prove by contradiction";
MessageName[ forallGoal, "usage", lang] = "Prove universally quantified goal";
MessageName[ forallKB, "usage", lang] = "Instantiate universally quantified formula";
MessageName[ existsGoal, "usage", lang] = "Prove existentially quantified goal by introducing meta variables";
MessageName[ existsKB, "usage", lang] = "Instantiate existentially quantified formula";

] (* With *)


(* ::Section:: *)
(* Private Implementation Part: executes in Theorema`Provers`Private` *)

Begin["`Private`"]

With[ {lang = "English"},

translate[ "Quantifier Rules", lang] = "Quantifier Rules";
translate[ "Basic Theorema Language Rules", lang] = "Basic Theorema Language Rules";
translate[ "Connectives Rules", lang] = "Rules for Logical Connectives";
translate[ "Equality Rules", lang] = "Rules for Equality";
translate[ "Termination Rules", lang] = "Rules for Proof Termination";

proofStepText[ contradictionKB, lang, {{k_, c_}}, {}, pVal_] := {textCell[ "The proof is finished, because ", formulaReference[ k], 
	" contradicts ", formulaReference[ c], "."]
    };

proofStepText[ falseInKB, lang, {{k_}}, {}, pVal_] := {textCell[ "The proof is finished, because ", formulaReference[ k], 
	" is a contradiction in the knowledge base."]
    };

proofStepText[ goalInKB, lang, {{goal_, k_}}, {}, pVal_] := {textCell[ "The goal ", formulaReference[ goal], 
	" is identical to formula ", formulaReference[ k], " in the knowledge base. Thus, the proof is finished."]
    };

proofStepText[ trueGoal, lang, {{goal_}}, {}, pVal_] := {textCell[ "The proof is finished, because the goal ", formulaReference[ goal], 
	" is true."]
    };

proofStepText[ notGoal|contradiction, lang, {{g_}}, {{opp_}}, ___] := {textCell[ "We prove ", formulaReference[ g], " by contradiction, i.e. we assume"],
	assumptionCell[ opp],
	textCell[ "and derive a contradiction."]
	};

proofStepText[ andGoal, lang, {{g_}}, _, ___] := {textCell[ "For proving ", formulaReference[ g], " we prove the individual conjuncts."]};

subProofHeader[ andGoal, lang, _, {generated_List}, pVal_, {p_}] := {textCell[ "Proof of ", formulaReference[ Part[ generated, p]], ":"],
	textCell[ "We need to prove"],
	goalCell[ Part[ generated, p], "."]
	};

proofStepText[ andKB, lang, {{g_}}, {generated_List}, ___] := {textCell[ "We split the conjunction ", formulaReference[ g], " and add"],
	assumptionListCells[ generated, ",", ""],
	textCell[ "to the knowledge base."]
	};

proofStepText[ orGoal, lang, {{g_}}, {{negAssum__, newG_}}, ___] := {textCell[ "For proving the disjunction ", formulaReference[ g], " we assume"],
	assumptionListCells[ {negAssum}, ",", ""],
	textCell[ "and show"],
	goalCell[ newG, "."]
	};

proofStepText[ orKB, lang, {{g_}}, {generated_List}, ___] := {textCell[ "Based on the assumption ", formulaReference[ g], " we distinguish several cases:"]};

subProofHeader[ orKB, lang, _, {generated_List}, pVal_, {p_}] := {textCell[ "Case ", ToString[p], ": we assume"],
	assumptionCell[ Part[ generated, p], "."]
	};

proofStepText[ implGoalDirect, lang, {{g_}}, {{l_, r_}}, ___] := {textCell[ "In order to prove ", formulaReference[ g], " we assume"],
	assumptionCell[ l],
	textCell[ "and then prove"],
	goalCell[ r, "."]
	};

proofStepText[ implGoalCP, lang, {{g_}}, {{nr_, nl_}}, ___] := {textCell[ "We prove ", formulaReference[ g], " by contraposition, i.e. we assume"],
	assumptionCell[ nr],
	textCell[ "and prove"],
	goalCell[ nl, "."]
	};

proofStepText[ equivGoal, lang, {{g_}}, _, ___] := {textCell[ "We prove both directions of ", formulaReference[ g], "."]};

subProofHeader[ equivGoal, lang, _, _, pVal_, {p_}] := {textCell[ Switch[ p, 1, "\[RightArrow]", 2, "\[LeftArrow]"], ":"]};

proofStepText[ forallGoal, lang, {{g_}}, {{newG_}}, ___, "abf" -> v_List, ___] := {textCell[ "For proving ", formulaReference[ g], " we choose ", 
	inlineTheoremaExpressionSeq[ v], " arbitrary but fixed and show"],
	goalCell[ newG, "."]
	};

proofStepText[ forallGoal, lang, {{g_}}, {{newG_, assum__}}, ___, "abf" -> v_List, ___] := {textCell[ "For proving ", formulaReference[ g], " we choose ", 
	inlineTheoremaExpressionSeq[ v], " arbitrary but fixed and assume"],
	assumptionListCells[ {assum}, ",", "."],
	textCell[ "We have to show"],
	goalCell[ newG, "."]
	};

proofStepText[ forallGoal, lang, {{g_}}, {{simpG_}}, ___] := {textCell[ "The universally quantified goal ", formulaReference[ g], " simplifies to"],
	goalCell[ simpG, "."]
	};

proofStepText[ existsGoal, lang, {{g_}}, {{newG_}}, ___, "meta" -> v_List, ___] := {textCell[ "For proving ", formulaReference[ g], " we have to find ",
	If[ Length[v] == 1, "an appropriate value for ", "appropriate values for "],
	inlineTheoremaExpressionSeq[ v], ", such that we can prove"],
	goalCell[ newG, "."]
	};

proofStepText[ existsGoal, lang, {{g_}}, {{simpG_}}, ___] := {textCell[ "The existentially quantified goal ", formulaReference[ g], " simplifies to"],
	goalCell[ simpG, "."]
	};
	
proofStepText[ existsKB, lang, {{e_}}, {new_List}, ___, "abf" -> v_List, ___] := {textCell[ "From ", formulaReference[ e], " we know "], 
	assumptionListCells[ new, ",", ""],
	textCell[ " for arbitrary but fixed ", inlineTheoremaExpressionSeq[ v], "."]
	};

proofStepText[ existsKB, lang, {{g_}}, {{simpG_}}, ___] := {textCell[ "The universally quantified goal ", formulaReference[ g], " simplifies to"],
	goalCell[ simpG, "."]
	};
	
] (* With *)

End[]