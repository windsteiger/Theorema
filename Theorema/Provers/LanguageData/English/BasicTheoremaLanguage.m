
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
MessageName[ forallKBInteractive, "usage", lang] = "Interactively instantiate universally quantified formula";
MessageName[ instantiate, "usage", lang] = "Instantiate universally quantified formula";
MessageName[ existsGoal, "usage", lang] = "Prove existentially quantified goal by introducing meta variables";
MessageName[ existsGoalInteractive, "usage", lang] = "Prove existentially quantified goal by interactive instantiation";
MessageName[ existsKB, "usage", lang] = "Instantiate existentially quantified formula";
MessageName[ multipleGoalRewriting, "usage", lang] = "Goal can be rewritten in several ways";
MessageName[ goalRewriting, "usage", lang] = "Goal rewriting based on (quantified) implications and equivalences in the knowledge base";
MessageName[ knowledgeRewriting, "usage", lang] = "Knowledge rewriting based on (quantified) implications and equivalences in the knowledge base";
MessageName[ elementarySubstitution, "usage", lang] = "Elementary substitution based on equalities and equivalences in the knowledge base";
MessageName[ expandDef, "usage", lang] = "Expand definitions";
MessageName[ eqGoal, "usage", lang] = "Prove equalities";
MessageName[ instantiate, "usage", lang] = "Instantiate using constants available in the proof";

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

subProofHeader[ andGoal, lang, _, {generated_List}, ___, pVal_, {p_}] := {textCell[ "Proof of ", formulaReference[ Part[ generated, p]], ":"],
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

subProofHeader[ orKB, lang, _, {generated_List}, ___, pVal_, {p_}] := {textCell[ "Case ", ToString[p], ": we assume"],
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

subProofHeader[ equivGoal, lang, _, _, ___, pVal_, {p_}] := {textCell[ Switch[ p, 1, "\[DoubleRightArrow]", 2, "\[DoubleLeftArrow]"], ":"]};

proofStepText[ forallGoal, lang, {{g_}}, {{newG_}}, ___, "abf" -> v_List, ___] := {textCell[ "For proving ", formulaReference[ g], " we choose ", 
	inlineTheoremaExpressionSeq[ v, lang], " arbitrary but fixed and show"],
	goalCell[ newG, "."]
	};

proofStepText[ forallGoal, lang, {{g_}}, {{newG_, assum__}}, ___, "abf" -> v_List, ___] := {textCell[ "For proving ", formulaReference[ g], " we choose ", 
	inlineTheoremaExpressionSeq[ v, lang], " arbitrary but fixed and assume"],
	assumptionListCells[ {assum}, ",", "."],
	textCell[ "We have to show"],
	goalCell[ newG, "."]
	};

proofStepText[ forallGoal, lang, {{g_}}, {{simpG_}}, ___] := {textCell[ "The universally quantified goal ", formulaReference[ g], " simplifies to"],
	goalCell[ simpG, "."]
	};

proofStepText[ forallKB, lang, {{u_}}, {}, ___] := 
	(* Instantiation has been tried, but was not successful *)
	{textCell[ "No instantiation of ", formulaReference[ u], " possible."]};
	
proofStepText[ forallKB, lang, {{u_}}, {g_}, ___, "instantiation" -> inst_List, ___] :=
    Module[ {instText = {textCell[ "We instantiate ", formulaReference[ u], ":"]}, i},
        Do[
            instText = Join[ instText,
                {textCell[ "Using ", inlineTheoremaExpression[ inst[[ i]]], " we obtain"],
                assumptionCell[ g[[ i]], "."]}],
            {i, Length[ g]}
        ];
        instText
    ];

proofStepText[ forallKBInteractive, lang, {{u_}}, {{g_}}, ___, "instantiation" -> inst_List, ___] :=
	{textCell[ "Formula ", formulaReference[ u], " holds in particular for ", inlineTheoremaExpressionSeq[ inst, lang], ", i.e."],
	assumptionCell[ g, "."]
    };

proofStepText[ existsGoal, lang, {{g_}}, {{newG_}}, ___, "meta" -> v_List, ___] := {textCell[ "For proving ", formulaReference[ g], " we have to find ",
	If[ Length[v] == 1, "an appropriate value for ", "appropriate values for "],
	inlineTheoremaExpressionSeq[ v, lang], ", such that we can prove"],
	goalCell[ newG, "."]
	};

proofStepText[ existsGoal, lang, {{g_}}, {{simpG_}}, ___] := {textCell[ "The existentially quantified goal ", formulaReference[ g], " simplifies to"],
	goalCell[ simpG, "."]
	};
	
proofStepText[ existsGoalInteractive, lang, {{g_}}, {{newG_}}, ___, "instantiation" -> v:{___Rule}, ___] := {textCell[ "For proving ", formulaReference[ g], 
	", let ", inlineTheoremaExpressionSeq[ Apply[ EqualDef$TM, v, {1}], lang]," and then prove "],
	goalCell[ newG, "."]
	};

proofStepText[ existsKB, lang, {{e_}}, {new_List}, ___, "abf" -> v_List, ___] := {textCell[ "From ", formulaReference[ e], " we know "], 
	assumptionListCells[ new, ",", ""],
	textCell[ " for arbitrary but fixed ", inlineTheoremaExpressionSeq[ v, lang], "."]
	};

proofStepText[ existsKB, lang, {{g_}}, {{simpG_}}, ___] := {textCell[ "The universally quantified goal ", formulaReference[ g], " simplifies to"],
	goalCell[ simpG, "."]
	};

proofStepText[ multipleGoalRewriting, lang, ___] := {textCell[ "We have several possibilities to rewrite the goal."]};

subProofHeader[ multipleGoalRewriting, lang, u_, g_, ___, pVal_, {p_}] := {};

proofStepText[ goalRewriting, lang, {}, {}, ___] := {};
(* Case: goal rewriting applicable, but no rewrite possible *)	

proofStepText[ goalRewriting, lang, {{origGoal_, rewrittenBy_}}, {{g_}}, ___] := 
(* Case: no condition generated *)
	{textCell[ "By ", formulaReference[ rewrittenBy], " the goal ", formulaReference[ origGoal], " can be reduced to"],
	goalCell[ g, "."]};
	
proofStepText[ knowledgeRewriting, lang, {}, {}, ___] := {};
(* Case: knowledge rewriting applicable, but no rewrite possible *)	

proofStepText[ knowledgeRewriting, lang, u_, g_, ___] := 
(* Case: new knowledge generated *)
    Module[ {stepText = {textCell["We augment the knowledge base:"]}, j},
        Do[
            stepText = Append[ stepText, 
            	cellGroup[ {textCell[ "From ", formulaReference[ u[[j, 1]]], ", using ", formulaReferenceSequence[ Rest[ u[[j]]], lang], ", we can deduce "],
            		assumptionListCells[ g[[j]], ",", "."]}]],
            {j, Length[ g]}
        ];
        stepText
    ];
	
proofStepText[ elementarySubstitution, lang, u_, g_, ___, "usedSubst" -> subs_List, ___] := 
	(* u, g, and subs have same length.
	   u is a list of singleton lists, u[[i,1]] are the formulae that are rewritten
	   g is a list of singleton lists, g[[i,1]] are the new formulae
	   subs is an auxliliary list containing lists of formulae, namely subs[[i]] are the formulae used when rewriting u[[i,1]] to g[[i,1]] *)
	Module[ {stepText = {}, j, repl},
		(* If the first in u and g are the same, then the goal has not been rewritten *)
		If[ u[[1]] =!= g[[1]],
			repl = subs[[1]];
			stepText = { textCell[ "In order to prove ", formulaReference[ u[[1, 1]]], ", using ", 
				formulaReferenceSequence[ repl, lang], ", we now have to show"],
				goalCell[ g[[1, 1]], "."]}
		];
		PrependTo[ stepText, textCell[ "We apply substitutions:"]];
		(* Each of the remaining is an expansion in the KB. Produce a line of text for each of them *)
		Do[
			repl = subs[[j]];
			suffix = If[ Length[ repl] == 1, "", "s"];
			stepText = Join[ stepText, 
				{textCell[ "From ", formulaReference[ u[[j, 1]]], " we know, by ", formulaReferenceSequence[ repl, lang], ","], 
				assumptionCell[ g[[j, 1]]]}],
			{j, 2, Length[g]}
		];
		stepText
	];
	
proofStepText[ expandDef, lang, u:{___, {}}, g:{___, {True}}, ___, "usedDefs" -> defs_List, ___] := 
	(* u, g, and defs have same length.
	   Except for the last element, u is a list of singleton lists, u[[i,1]] are the formulae that are rewritten
	   Except for the last element, g is a list of singleton lists, g[[i,1]] are the new formulae
	   defs is an auxliliary list containing lists of definition formulae, namely defs[[i]] are the definitions used when rewriting u[[i,1]] to g[[i,1]].
	   According to the input pattern, this is the case, where NO CONDITIONS need to be checked.
	*)
	Module[ {stepText = {}, j, repl, suffix},
		(* If the first in u and g are the same, then the goal has not been rewritten *)
		If[ u[[1]] =!= g[[1]],
			repl = defs[[1]];
			suffix = If[ Length[ repl] == 1, "", "s"];
			stepText = { textCell[ "In order to prove ", formulaReference[ u[[1, 1]]], ", using definition" <> suffix <> " ", 
				formulaReferenceSequence[ repl, lang], ", we now have to show"],
				goalCell[ g[[1, 1]], "."]}
		];
		PrependTo[ stepText, textCell[ "We expand definitions:"]];
		(* Each of the remaining is an expansion in the KB. Produce a line of text for each of them *)
		Do[
			repl = defs[[j]];
			suffix = If[ Length[ repl] == 1, "", "s"];
			stepText = Join[ stepText, 
				{textCell[ "From ", formulaReference[ u[[j, 1]]], " we know, by definition" <> suffix <> " ", formulaReferenceSequence[ repl, lang], ","], 
				assumptionCell[ g[[j, 1]]]}],
			{j, 2, Length[g]-1}
		];
		stepText
	];

proofStepText[ expandDef, lang, u_, g:_, ___, "usedDefs" -> defs_List, ___] := {textCell[ "We expand definitions:"]};

subProofHeader[ expandDef, lang, u_, g_, ___, "usedDefs" -> defs_List, ___, {1}] := 
	Module[ {stepText = {}, j, repl, suffix},
		(* If the first in u and g are the same, then the goal has not been rewritten *)
		If[ u[[1]] =!= g[[1]],
			repl = defs[[1]];
			suffix = If[ Length[ repl] == 1, "", "s"];
			stepText = { textCell[ "In order to prove ", formulaReference[ u[[1, 1]]], ", using definition" <> suffix <> " ", 
				formulaReferenceSequence[ repl, lang], ", we now have to show"],
				goalCell[ g[[1, 1]], "."]}
		];
		(* Each of the remaining is an expansion in the KB. Produce a line of text for each of them *)
		Do[
			repl = defs[[j]];
			suffix = If[ Length[ repl] == 1, "", "s"];
			stepText = Join[ stepText, 
				{textCell[ "From ", formulaReference[ u[[j, 1]]], " we know, by definition" <> suffix <> " ", formulaReferenceSequence[ repl, lang], ","], 
				assumptionCell[ g[[j, 1]]]}],
			{j, 2, Length[g]-1}
		];
		stepText
	];
subProofHeader[ expandDef, lang, u_, {___, {cond_}}, ___, "usedDefs" -> defs_List, ___, {2}] := {textCell[ "In order to validate the expansion of the definitions above, we have to check"],
	goalCell[ cond, "."]
	};	
	
proofStepText[ instantiate, lang, u_, {}, ___] := 
	(* Instantiation has been tried, but none of them could be successfully applied *)
	{textCell[ "New constants have been generated, but no instantiations could be carried out."]};
	
proofStepText[ instantiate, lang, u_, g_, ___, "instantiation" -> inst_List, ___] := 
	Module[ {stepText = {textCell[ "There are new constants to be used for instantiation."]}, instText = {}, j, i},
		(* Each of the g_i is a list of instances of u_i *)
		Do[
			instText = {textCell[ "We can instantiate ", formulaReference[ u[[j, 1]]], ":"]};
			Do[
				instText = Join[ instText,
					{textCell[ "With ", inlineTheoremaExpression[ inst[[j, i]]], " we get"],
					assumptionCell[ g[[j, i]], "."]}],
				{i, Length[ g[[j]]]}
			];
			stepText = Append[ stepText, cellGroup[ instText]],
			{j, Length[u]}
		];
		stepText
	]
	
] (* With *)

End[]