(* Theorema 
    Copyright (C) 1995-2014 The Theorema Group

    This file is part of Theorema 2.0
    
    Theorema 2.0 is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Theorema 2.0 is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program. If not, see <http://www.gnu.org/licenses/>.
*)

(*
   *********************************************************************************************
   -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- 
   *********************************************************************************************
 
     If you modify this file, then insert the new translation in correct alphabetical 
     order (case-insensitive).

     ALSO, YOU MUST add a corresponding entry in the respective file for each other language, 
     either
      1) in the respective section named "UNTRANSLATED", note there are several such sections
         in the file (in case you cannot or do not want to provide a translation) or
      2) in correct alphabetical order (case-insensitive) in case you immediately provide 
         a translation.
      
   *********************************************************************************************
   -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- 
   *********************************************************************************************
 *)
 
(* ::Section:: *)
(* Public Declaration Part: executes in Theorema`Provers` *)

With[ {lang = "English"},

	MessageName[ andGoal, "usage", lang] = "Split a conjunction in the goal";
	MessageName[ andKB, "usage", lang] = "Split a conjunction in the knowledge base";

	MessageName[ basicTheoremaLanguageRules, "usage", lang] = "Rules for the basic language constructs from the Theorema language, standard propositional and predicate logic";

	MessageName[ contradictionKB, "usage", lang] = "Knowledge base contains contradicting formulae";
	MessageName[ contradictionUniv1, "usage", lang] = "Knowledge base contains a universally quantified formulae that contradicts some other formula.";
	MessageName[ contradictionUniv2, "usage", lang] = "Knowledge base contains two contradicting universally quantified formulas.";
	MessageName[ contradiction, "usage", lang] = "Prove by contradiction";

	MessageName[ deMorganKB, "usage", lang] = "Apply de'Morgan's law";

	MessageName[ elementarySubstitution, "usage", lang] = "Elementary substitution based on equalities and equivalences in the knowledge base";
	MessageName[ eqGoal, "usage", lang] = "Prove equalities";
	MessageName[ equivGoal, "usage", lang] = "Prove equivalence by double implication";
	MessageName[ existsGoalInteractive, "usage", lang] = "Prove existentially quantified goal by interactive instantiation";
	MessageName[ existsGoal, "usage", lang] = "Prove existentially quantified goal by introducing meta variables";
	MessageName[ existsKB, "usage", lang] = "Skolemize existentially quantified knowledge";
	MessageName[ expandDef, "usage", lang] = "Expand explicit definitions";

	MessageName[ falseInKB, "usage", lang] = "Knowledge base contains a formula False";
	MessageName[ forallGoal, "usage", lang] = "Prove universally quantified goal";
	MessageName[ forallKBInteractive, "usage", lang] = "Interactively instantiate universally quantified knowledge";
	MessageName[ forallKB, "usage", lang] = "Instantiate new universally quantified knowledge";

	MessageName[ goalInKB, "usage", lang] = "Knowledge base contains the proof goal";
	MessageName[ goalRewriting, "usage", lang] = "Goal rewriting based on (quantified) implications and equivalences in the knowledge base";

	MessageName[ implGoalCP, "usage", lang] = "Prove implication using contraposition";
	MessageName[ implGoalDirect, "usage", lang] = "Prove implication directly";
	MessageName[ implicitDef, "usage", lang] = "Handle implicit function definitions";
	MessageName[ implKBCases, "usage", lang] = "Case distinction based on an implication in the knowledge base";
	MessageName[ inequality1, "usage", lang] = "Inequality rules";
	MessageName[ instantiate, "usage", lang] = "Instantiate universally quantified knowledge with new constants";

	MessageName[ knowledgeRewriting, "usage", lang] = "Knowledge rewriting based on (quantified) implications and equivalences in the knowledge base";

	MessageName[ maxTuples1, "usage", lang] = "Maximum rules for tuples";
	MessageName[ memberCases, "usage", lang] = "Case distinction based on membership";
	MessageName[ multipleGoalRewriting, "usage", lang] = "Goal can be rewritten in several ways";

	MessageName[ notGoal, "usage", lang] = "Prove negation by contradiction";

	MessageName[ orGoal, "usage", lang] = "Prove disjunction";
	MessageName[ orKB, "usage", lang] = "Case distinction based on a disjunction in the knowledge base";

	MessageName[ partSolveMetaMatching, "usage", lang] = "Instantiate meta-variables by matching";
	MessageName[ partSolveMetaMultiMatching, "usage", lang] = "Instantiate meta-variables by matching (multiple matching)";

	MessageName[ quantifierRules, "usage", lang] = "Rules for quantifiers";

	MessageName[ solveMetaUnification, "usage", lang] = "Instantiate meta-variables by unification";
	MessageName[ specialArithmeticRules, "usage", lang] = "Rules for special arithmetic constructs";

	MessageName[ trueGoal, "usage", lang] = "The proof goal is True";

] (* With *)


(* ::Section:: *)
(* Private Implementation Part: executes in Theorema`Provers`Private` *)

Begin["`Private`"]


With[ {lang = "English"},

	translate[ "Basic Theorema Language Rules", lang] = "Basic Theorema Language Rules";
	translate[ "Connectives Rules", lang] = "Rules for Logical Connectives";
	translate[ "Equality Rules", lang] = "Rules for Equality";
	translate[ "Quantifier Rules", lang] = "Quantifier Rules";
	translate[ "Rewriting Rules", lang] = "Rules based on Rewriting";
	translate[ "Special Arithmetic", lang] = "Special Arithmetic";
	translate[ "Termination Rules", lang] = "Rules for Proof Termination";

(* ::Subsection:: *)
(* A *)

proofStepText[ andGoal, lang, {{g_}}, _, ___] := {textCell[ "For proving ", formulaReference[ g], " we prove the individual conjuncts."]};

subProofHeader[ andGoal, lang, _, {generated_List}, ___, pVal_, {p_}] := {textCell[ "Proof of ", formulaReference[ Part[ generated, p]], ":"],
	textCell[ "We need to prove"],
	goalCell[ Part[ generated, p], "."]
	};

proofStepText[ andKB, lang, {{g_}}, {generated_List}, ___] := {textCell[ "We split the conjunction ", formulaReference[ g], " and add"],
	assumptionListCells[ generated, ",", ""],
	textCell[ "to the knowledge base."]
	};

(* ::Subsection:: *)
(* C *)

proofStepText[ contradictionKB, lang, {{k_, c_}}, {}, pVal_] := {textCell[ "This part of the proof is herewith finished, because ", formulaReference[ k], 
	" contradicts ", formulaReference[ c], "."]
    };

proofStepText[ contradictionUniv1, lang, {{u_, c_}}, {}, ___, "instantiation" -> inst_List, ___, pVal_] := {textCell[ "This part of the proof is herewith finished, because instantiating ", formulaReference[ u], 
	" by ", inlineTheoremaExpressionSeq[ inst, lang], " contradicts ", formulaReference[ c], "."]
    };

proofStepText[ contradictionUniv2, lang, {{u_, c_}}, {}, ___, "instantiation" -> inst_List, ___, pVal_] := {textCell[ "This part of the proof is herewith finished, because instantiating ", formulaReference[ u], 
	" and ", formulaReference[ c], " by ", inlineTheoremaExpressionSeq[ inst, lang], " gives a contradiction."]
    };

(* ::Subsection:: *)
(* D *)

proofStepText[ deMorganKB, lang, used_, generated_, ___, pVal_] := {textCell[ "Using de'Morgan's law, the formulas ", 
	formulaReferenceSequence[ Flatten[ used], lang],
	" can be transformed into"],
	assumptionListCells[ Flatten[ generated], ",", "."]
    };

(* ::Subsection:: *)
(* E *)

proofStepText[ elementarySubstitution, lang, u_, g_, ___, "goalRewrite" -> gr_, "usedSubst" -> subs_List, ___] := 
	(* u, g, and subs have same length.
	   u is a list of singleton lists, u[[i,1]] are the formulae that are rewritten
	   g is a list of singleton lists, g[[i,1]] are the new formulae
	   subs is an auxliliary list containing lists of formulae, namely subs[[i]] are the formulae used when rewriting u[[i,1]] to g[[i,1]] *)
	Module[ {stepText = {}, j, repl, startKB = 1, suffix},
		If[ gr,
			(* the goal has been rewritten *)
			repl = subs[[1]];
			stepText = {textCell[ "In order to prove ", formulaReference[ u[[1, 1]]], ", using ", 
				formulaReferenceSequence[ repl, lang], ", we now show"],
				goalCell[ g[[1, 1]], "."]};
			startKB = 2 (* the first generated is the rewritten goal, kb rewriting starts from the second generated onwards *)
		];
		PrependTo[ stepText, textCell[ "We apply substitutions:"]];
		(* Each of the remaining is an expansion in the KB. Produce a line of text for each of them *)
		Do[
			repl = subs[[j]];
			suffix = If[ Length[ repl] == 1, "", "s"];
			stepText = Join[ stepText, 
				{textCell[ "From ", formulaReference[ u[[j, 1]]], " we know, by ", formulaReferenceSequence[ repl, lang], ","], 
				assumptionCell[ g[[j, 1]]]}],
			{j, startKB, Length[g]}
		];
		stepText
	];
	
proofStepText[ equivGoal, lang, {{g_}}, _, ___] := {textCell[ "We prove both directions of ", formulaReference[ g], "."]};

subProofHeader[ equivGoal, lang, _, _, ___, pVal_, {p_}] := {textCell[ Switch[ p, 1, "\[DoubleRightArrow]", 2, "\[DoubleLeftArrow]"], ":"]};

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
	textCell[ " for some ", inlineTheoremaExpressionSeq[ v, lang], "."]
	};

proofStepText[ existsKB, lang, {{g_}}, {{simpG_}}, ___] := {textCell[ "The universally quantified goal ", formulaReference[ g], " simplifies to"],
	goalCell[ simpG, "."]
	};

proofStepText[ expandDef, lang, u_List, g_List, ___, "defCond" -> False, "usedDefs" -> defs_List, ___] := 
	(* u, g, and defs have same length.
	   u is a list of singleton lists, u[[i,1]] are the formulas that are rewritten
	   g is a list of singleton lists, g[[i,1]] are the new formulas
	   defs is an auxliliary list containing lists of definition formulas, namely defs[[i]] are the definitions used when rewriting u[[i,1]] to g[[i,1]].
	   According to the "defCond" -> False, this is the case, where NO CONDITIONS need to be checked.
	*)
	Module[ {stepText = {}, j, repl, suffix},
		(* If the first in u and g are the same, then the goal has not been rewritten *)
		If[ u[[1]] =!= g[[1]],
			repl = defs[[1]];
			suffix = If[ Length[ repl] == 1, "", "s"];
			stepText = { textCell[ "In order to prove ", formulaReference[ u[[1, 1]]], ", using definition" <> suffix <> " ", 
				formulaReferenceSequence[ repl, lang], ", we now show"],
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
			{j, 2, Length[ g]}
		];
		stepText
	];

proofStepText[ expandDef, lang, u_, g_, ___, "defCond" -> True, "usedDefs" -> defs_List, ___] := {textCell[ "We expand definitions:"]};

subProofHeader[ expandDef, lang, u_, g_, ___, "defCond" -> True, "usedDefs" -> defs_List, ___, {1}] := 
	Module[ {stepText = {}, j, repl, suffix},
		(* If the first in u and g are the same, then the goal has not been rewritten *)
		If[ u[[1]] =!= g[[1]],
			repl = defs[[1]];
			suffix = If[ Length[ repl] == 1, "", "s"];
			stepText = {textCell[ "In order to prove ", formulaReference[ u[[1, 1]]], ", using definition" <> suffix <> " ", 
				formulaReferenceSequence[ repl, lang], ", we now show"],
				goalCell[ g[[1, 1]], "."]}
		];
		(* Each of the remaining is an expansion in the KB. Produce a line of text for each of them *)
		Do[
			repl = defs[[j]];
			suffix = If[ Length[ repl] == 1, "", "s"];
			stepText = Join[ stepText, 
				{textCell[ "From ", formulaReference[ u[[j, 1]]], " we know, by definition" <> suffix <> " ", formulaReferenceSequence[ repl, lang], ","], 
				assumptionCell[ g[[j, 1]]]}],
			{j, 2, Length[ g] - 1} (* the last is the new goal for a condition in the rewrite -> we go only to Length-1 *)
		];
		stepText
	];

subProofHeader[ expandDef, lang, u_, {___, {cond_}}, ___, "defCond" -> True, "usedDefs" -> defs_List, ___, {2}] := {
	textCell[ "In order to validate the expansion of the definitions above, we have to check"],
	goalCell[ cond, "."]
	};	

(* ::Subsection:: *)
(* F *)

proofStepText[ falseInKB, lang, {{k_}}, {}, pVal_] := {textCell[ "Thus, this part of the proof is finished, because ", formulaReference[ k], 
	" is a contradiction in the knowledge base."]
    };

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

(* ::Subsection:: *)
(* G *)

proofStepText[ goalInKB, lang, {{goal_, k_}}, {}, pVal_] := {textCell[ "The goal ", formulaReference[ goal], 
	" is identical to formula ", formulaReference[ k], " in the knowledge base. Thus, this part of the proof is finished."]
    };

proofStepText[ goalRewriting, lang, {}, {}, ___] := {textCell[ "No goal rewriting."]};
(* Case: goal rewriting applicable, but no rewrite possible *)	

proofStepText[ goalRewriting, lang, {{origGoal_, rewrittenBy_}}, {{g_}}, ___] := 
(* Case: no condition generated *)
	{textCell[ "By ", formulaReference[ rewrittenBy], " the goal ", formulaReference[ origGoal], " can be reduced to"],
	goalCell[ g, "."]};
	
(* ::Subsection:: *)
(* I *)

proofStepText[ implGoalCP, lang, {{g_}}, {{nr_, nl_}}, ___] := {textCell[ "We prove ", formulaReference[ g], " by contraposition, i.e. we assume"],
	assumptionCell[ nr],
	textCell[ "and prove"],
	goalCell[ nl, "."]
	};

proofStepText[ implGoalDirect, lang, {{g_}}, {{l_, r_}}, ___] := {textCell[ "In order to prove ", formulaReference[ g], " we assume"],
	assumptionCell[ l],
	textCell[ "and then prove"],
	goalCell[ r, "."]
	};

proofStepText[ implicitDef, lang, {}, {}, ___] := {};

proofStepText[ implicitDef, lang, u_, g_, ___, "introConstFor" -> termConst_List, ___] := 
	Module[ {stepText, j},
		stepText = {textCell[ "For the implicitly defined function ", formulaReference[ u[[1, 1]]], " we introduce new constants ", 
			inlineTheoremaExpressionSeq[ Apply[ EqualDef$TM, termConst, {1}], lang], " such that"],
			assumptionListCells[ g[[1]], ",", "."]};
		(* g[[2]] is the new goal. {} if no rewrite happened in the goal *)
		If[ g[[2]] =!= {},
			stepText = Join[ stepText,
				{textCell[ "For proving ", formulaReference[ u[[2, 1]]], ", due to ", formulaReferenceSequence[ Rest[ u[[2]]], lang], ", it suffices now to prove"],
				goalCell[ g[[2, 1]], "."]}
			]
		];
		(* Each of the remaining is an expansion in the KB. Produce a line of text for each of them *)
		Do[
			stepText = Join[ stepText, 
				{textCell[ "The assumption ", formulaReference[ u[[j, 1]]], " becomes (due to ", formulaReferenceSequence[ Rest[ u[[j]]], lang], ")"], 
				assumptionCell[ g[[j, 1]]]}],
			{j, 3, Length[g]}
		];
		stepText
	];

proofStepText[ implKBCases, lang, {{g_}}, {{_, _}}, ___] := {textCell[ "Based on the assumption ", formulaReference[ g], " we distinguish several cases:"]};

subProofHeader[ implKBCases, lang, _, {generated:{_, _}}, ___, pVal_, {p_}] := {textCell[ "Case ", ToString[ p], ": we assume"],
	assumptionCell[ Part[ generated, p], "."]
	};

proofStepText[ inequality1, lang, {{g_, k_}}, {}, ___] := 
	{textCell[ "Due to ", formulaReference[ k], " the goal ", formulaReference[ g], " is true."]};	
	
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
					{textCell[ "With ", inlineTheoremaExpressionSeq[ inst[[j, i]], lang], " we get"],
					assumptionCell[ g[[j, i]], "."]}],
				{i, Length[ g[[j]]]}
			];
			stepText = Append[ stepText, cellGroup[ instText]],
			{j, Length[u]}
		];
		stepText
	];

(* ::Subsection:: *)
(* K *)

proofStepText[ knowledgeRewriting, lang, {}, {}, ___] := {textCell[ "No knowledge rewriting."]};
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

(* ::Subsection:: *)
(* M *)

proofStepText[ maxTuples1, lang, {{g_}}, {}, ___, "comp" -> {t1_, t2_, e_, m_}, ___] := 
	{textCell[ "The tuple ", inlineTheoremaExpression[ t1], 
		" contains the same elements like ", inlineTheoremaExpression[ t2], ", plus one more, namely ",
		inlineTheoremaExpression[ e], ". Hence, ", inlineTheoremaExpression[ m], 
		", which proves ", formulaReference[ g], "."]};

proofStepText[ memberCases, lang, {{k1_, k2_}, _}, _, ___] := {textCell[ "Based on ", formulaReference[ k1], " and ", formulaReference[ k2], " we distinguish two cases:"]};

subProofHeader[ memberCases, lang, _, {generated_List}, ___, pVal_, {p_}] := {textCell[ "Case ", ToString[ p], ": we assume"],
	assumptionCell[ Part[ generated, p], "."]
	};
	
proofStepText[ multipleGoalRewriting, lang, ___] := {textCell[ "We have several possibilities to rewrite the goal."]};

subProofHeader[ multipleGoalRewriting, lang, u_, g_, ___, pVal_, {p_}] := {};

(* ::Subsection:: *)
(* N *)

proofStepText[ notGoal|contradiction, lang, {{g_}}, {{opp_}}, ___] := {textCell[ "We prove ", formulaReference[ g], " by contradiction, i.e. we assume"],
	assumptionCell[ opp],
	textCell[ "and derive a contradiction."]
	};

(* ::Subsection:: *)
(* O *)

proofStepText[ orGoal, lang, {{g_}}, {{negAssum__, newG_}}, ___] := {textCell[ "For proving the disjunction ", formulaReference[ g], " we assume"],
	assumptionListCells[ {negAssum}, ",", ""],
	textCell[ "and show"],
	goalCell[ newG, "."]
	};

proofStepText[ orKB, lang, {{g_}}, {generated_List}, ___] := {textCell[ "Based on the assumption ", formulaReference[ g], " we distinguish several cases:"]};

subProofHeader[ orKB, lang, _, {generated_List}, ___, pVal_, {p_}] := {textCell[ "Case ", ToString[ p], ": we assume"],
	assumptionCell[ Part[ generated, p], "."]
	};

(* ::Subsection:: *)
(* P *)

proofStepText[ partSolveMetaMatching, lang, {{u_}}, {{g_}}, ___, "instantiation" -> inst_List, ___] := {
	textCell[ "Let now ", inlineTheoremaExpressionSeq[ inst[[1]], lang], ". In order to prove ", formulaReference[ u], " it suffices to show"],
	goalCell[ g, "."]
	};

proofStepText[ partSolveMetaMultiMatching, lang, {{u_}}, {{g__}}, ___, "instantiation" -> inst_List, ___] := {
	textCell[ "We have several choices."]
	};

subProofHeader[ partSolveMetaMultiMatching, lang, {{u_}}, {g_List}, ___, "instantiation" -> inst_List, ___, pVal_, {p_}] := {
	textCell[ "Let now ", inlineTheoremaExpressionSeq[ inst[[p]], lang], ". In order to prove ", formulaReference[ u], " it suffices to show"],
	goalCell[ g[[p]], "."]
	};

(* ::Subsection:: *)
(* S *)

proofStepText[ solveMetaUnification, lang, {{u_}}, {{g_}}, ___, "instantiation" -> inst_List, ___] := {
	textCell[ "Let now ", inlineTheoremaExpressionSeq[ inst[[ 1]], lang], ". In order to prove ", formulaReference[ u], " it suffices to show"],
	goalCell[ g, "."]
	};

proofStepText[ solveMetaUnification, lang, {{u_}}, {g_List}, ___, "instantiation" -> inst_List, ___] := 
	{textCell[ "We can instantiate."]};

subProofHeader[ solveMetaUnification, lang, {{u_}}, {g_List}, ___, "instantiation" -> inst_List, ___, {i_}] := {
	textCell[ "Let now ", inlineTheoremaExpressionSeq[ inst[[i]], lang], ". In order to prove ", formulaReference[ u], " it suffices to show"],
	goalCell[ g[[i]], "."]
	};	

(* ::Subsection:: *)
(* T *)

proofStepText[ trueGoal, lang, {{goal_}}, {}, pVal_] := {textCell[ "This part of the proof is now finished, because the goal ", formulaReference[ goal], 
	" is true."]
    };
	
		
] (* With *)

End[]
