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
 
     If you modify this file, then a new entry must have been added to the respective file in
     the "English" directory already.

     In this file, either
      1) copy the english entry into the corresponding section named "UNTRANSLATED" (there are
         several in this file 
	       or
      2) translate the english entry and add it in correct alphabetical order here 
         (case-insensitive).
      
   *********************************************************************************************
   -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- 
   *********************************************************************************************
 *)

(* ::Section:: *)
(* Public Declaration Part: executes in Theorema`Provers` *)

With[ {lang = "German"},
(* TRANSLATED *)
	MessageName[ andGoal, "usage", lang] = "Aufspalten von Konjunktionen im Beweisziel";
	MessageName[ andKB, "usage", lang] = "Aufspalten von Konjunktionen im Wissen";

	MessageName[ basicTheoremaLanguageRules, "usage", lang] = "Standard Beweisregeln f\[UDoubleDot]r grundlegende Konstrukte der Theorema Sprache, Aussagen- und Pr\[ADoubleDot]dikatenlogik";

	MessageName[ contradictionKB, "usage", lang] = "Widerspruch in der Wissensbasis";
	MessageName[ contradictionUniv1, "usage", lang] = "Eine universal quantifizierte Aussage in der Wissensbasis steht im Widerspruch zu einer anderen Aussage.";
	MessageName[ contradictionUniv2, "usage", lang] = "Zwei universal quantifizierte Aussagen in der Wissensbasis widersprechen einander.";
	MessageName[ contradiction, "usage", lang] = "Widerspruchsbeweis";

	MessageName[ deMorganKB, "usage", lang] = "De'Morgans Regel";

	MessageName[ elementarySubstitution, "usage", lang] = "Elementare Substitutionen basierend auf Gleichheiten und \[CapitalADoubleDot]quivalenzen in der Wissensbasis";
	MessageName[ eqGoal, "usage", lang] = "Beweise Gleichheiten";
	MessageName[ equivGoal, "usage", lang] = "Beweise \[CapitalADoubleDot]quivalenz durch Implikation in beide Richtungen";
	MessageName[ existsGoalInteractive, "usage", lang] = "Beweise Existenzaussage durch interaktives Instanzieren";
	MessageName[ existsGoal, "usage", lang] = "Beweise Existenzaussage mit Meta-Variablen";
	MessageName[ existsKB, "usage", lang] = "Skolemisiere Existenzaussagen in der Wissensbasis";
	MessageName[ expandDef, "usage", lang] = "Expandiere explizite Definitionen";

	MessageName[ falseInKB, "usage", lang] = "Wissensbasis enth\[ADoubleDot]lt False";
	MessageName[ forallGoal, "usage", lang] = "Beweise eine Allaussage";
	MessageName[ forallKBInteractive, "usage", lang] = "Interaktives Instanzieren von Allaussagen in der Wissensbasis";
	MessageName[ forallKB, "usage", lang] = "Instanzieren von neuen Allaussagen in der Wissensbasis";

	MessageName[ goalInKB, "usage", lang] = "Wissensbasis enth\[ADoubleDot]ltK das Beweisziel";
	MessageName[ goalRewriting, "usage", lang] = "Umformen des Beweisziels basierend auf (quantifizierten) Implikationen und \[CapitalADoubleDot]quivalenzen in der Wissensbasis";

	MessageName[ implGoalCP, "usage", lang] = "Beweise Implikation mittels Kontraposition";
	MessageName[ implGoalDirect, "usage", lang] = "Beweise Implikation direkt";
	MessageName[ implicitDef, "usage", lang] = "Behandle implizite Funktionsdefinitionen";
	MessageName[ implKBCases, "usage", lang] = "Fallunterscheidung basierend auf Implikation in der Wissensbasis";
	MessageName[ inequality1, "usage", lang] = "Ungleichungsregeln";
	MessageName[ instantiate, "usage", lang] = "Instanzieren Allaussagen in der Wissensbasis mit neuen Konstanten";

	MessageName[ knowledgeRewriting, "usage", lang] = "Umformen der Wissensbasis basierend auf (quantifizierten) Implikationen und \[CapitalADoubleDot]quivalenzen in der Wissensbasis";

	MessageName[ maxTuples1, "usage", lang] = "Maximum Regeln f\[UDoubleDot]r Tupel";
	MessageName[ multipleGoalRewriting, "usage", lang] = "Beweisziel kann auf verschiedene Arten umgeformt werden";

	MessageName[ notGoal, "usage", lang] = "Beweise Negation indirekt";

	MessageName[ orGoal, "usage", lang] = "Beweise eine Disjunktion";
	MessageName[ orKB, "usage", lang] = "Fallunterscheidung basierend auf Disjunktion in der Wissensbasis";

	MessageName[ partSolveMetaMatching, "usage", lang] = "Instanzieren von Meta-Variablen durch Matching";

	MessageName[ quantifierRules, "usage", lang] = "Regeln f\[UDoubleDot]r Quantoren";

	MessageName[ solveMetaUnification, "usage", lang] = "Instanzieren von Meta-Variablen durch Unifikation";
	MessageName[ specialArithmeticRules, "usage", lang] = "Regeln f\[UDoubleDot]r spezielle arithmetische Konstrukte";

	MessageName[ trueGoal, "usage", lang] = "Das Beweisziel ist True";
(* UNTRANSLATED *)

] (* With *)


(* ::Section:: *)
(* Private Implementation Part: executes in Theorema`Provers`Private` *)

Begin["`Private`"]


With[ {lang = "German"},
(* TRANSLATED *)
	translate[ "Basic Theorema Language Rules", lang] = "Grundlegende Regeln f\[UDoubleDot]r die Theorema Sprache";
	translate[ "Connectives Rules", lang] = "Junktorregeln";
	translate[ "Equality Rules", lang] = "Gleichheitsregeln";
	translate[ "Quantifier Rules", lang] = "Quantorenregeln";
	translate[ "Rewriting Rules", lang] = "Umformungsregeln";
	translate[ "Special Arithmetic", lang] = "Spezielle Arithmetik";
	translate[ "Termination Rules", lang] = "Regeln, die den Beweis beenden";
(* UNTRANSLATED *)

(* TRANSLATED *)

(* ::Subsection:: *)
(* A *)

proofStepText[ andGoal, lang, {{g_}}, _, ___] := {textCell[ "Um ", formulaReference[ g], " zu beweisen, zeigen wir die einzelnen Teile."]};

subProofHeader[ andGoal, lang, _, {generated_List}, ___, pVal_, {p_}] := {textCell[ "Beweis von ", formulaReference[ Part[ generated, p]], ":"],
	textCell[ "Wir haben zu zeigen"],
	goalCell[ Part[ generated, p], "."]
	};

proofStepText[ andKB, lang, {{g_}}, {generated_List}, ___] := {textCell[ "Wir spalten die Konjunktion ", formulaReference[ g], " auf und geben"],
	assumptionListCells[ generated, ",", ""],
	textCell[ "in die Wissensbasis."]
	};

(* ::Subsection:: *)
(* C *)

proofStepText[ contradictionKB, lang, {{k_, c_}}, {}, pVal_] := {textCell[ "Dieser Teil des Beweises ist damit fertig, weil ", formulaReference[ k], 
	" und ", formulaReference[ c], " einander widersprechen."]
    };

proofStepText[ contradictionUniv1, lang, {{u_, c_}}, {}, ___, "instantiation" -> inst_List, ___, pVal_] := {textCell[ "Dieser Teil des Beweises ist damit fertig, weil ", formulaReference[ u], 
	" instanziert mit ", inlineTheoremaExpressionSeq[ inst, lang], " und ", formulaReference[ c], " einander widersprechen."]
    };

proofStepText[ contradictionUniv2, lang, {{u_, c_}}, {}, ___, "instantiation" -> inst_List, ___, pVal_] := {textCell[ "Dieser Teil des Beweises ist damit fertig, weil ", formulaReference[ u], 
	" und ", formulaReference[ c], " instanziert mit ", inlineTheoremaExpressionSeq[ inst, lang], " einander widersprechen."]
    };

(* ::Subsection:: *)
(* D *)

proofStepText[ deMorganKB, lang, used_, generated_, ___, pVal_] := {textCell[ "Mithilfe der Gesetze von de'Morgan k\[ODoubleDot]nnen die Formeln ", 
	formulaReferenceSequence[ Flatten[ used], lang],
	" umgeformt werden zu"],
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
		(* If the first in u and g are the same, then the goal has not been rewritten *)
		If[ gr,
			repl = subs[[1]];
			stepText = { textCell[ "Um ", formulaReference[ u[[1, 1]]], " zu zeigen, zeigen wir wegen ", 
				formulaReferenceSequence[ repl, lang]],
				goalCell[ g[[1, 1]], "."]};
			startKB = 2 (* the first generated is the rewritten goal, kb rewriting starts from the second generated onwards *)
		];
		PrependTo[ stepText, textCell[ "Wir wenden Substitutionen an:"]];
		(* Each of the remaining is an expansion in the KB. Produce a line of text for each of them *)
		Do[
			repl = subs[[j]];
			suffix = If[ Length[ repl] == 1, "", "s"];
			stepText = Join[ stepText, 
				{textCell[ "Aus ", formulaReference[ u[[j, 1]]], " folgt, wegen ", formulaReferenceSequence[ repl, lang], ","], 
				assumptionCell[ g[[j, 1]]]}],
			{j, startKB, Length[g]}
		];
		stepText
	];
	
proofStepText[ equivGoal, lang, {{g_}}, _, ___] := {textCell[ "Wir beweisen beide Richtungen von ", formulaReference[ g], "."]};

subProofHeader[ equivGoal, lang, _, _, ___, pVal_, {p_}] := {textCell[ Switch[ p, 1, "\[DoubleRightArrow]", 2, "\[DoubleLeftArrow]"], ":"]};

proofStepText[ existsGoal, lang, {{g_}}, {{newG_}}, ___, "meta" -> v_List, ___] := {textCell[ "Wir wollen ", formulaReference[ g], " beweisen. Daher m\[UDoubleDot]ssen wir ",
	If[ Length[v] == 1, "einen geeigneten Wert f\[UDoubleDot]r ", "geeignete Werte f\[UDoubleDot]r "],
	inlineTheoremaExpressionSeq[ v, lang], " finden, sodass wir beweisen k\[ODoubleDot]nnen"],
	goalCell[ newG, "."]
	};

proofStepText[ existsGoal, lang, {{g_}}, {{simpG_}}, ___] := {textCell[ "Die Existenzaussage ", formulaReference[ g], " vereinfacht sich zu"],
	goalCell[ simpG, "."]
	};
	
proofStepText[ existsGoalInteractive, lang, {{g_}}, {{newG_}}, ___, "instantiation" -> v:{___Rule}, ___] := {textCell[ "Wir haben ", formulaReference[ g], 
	" zu zeigen. Sei nun ", inlineTheoremaExpressionSeq[ Apply[ EqualDef$TM, v, {1}], lang]." Wir bewiesen jetzt "],
	goalCell[ newG, "."]
	};

proofStepText[ existsKB, lang, {{e_}}, {new_List}, ___, "abf" -> v_List, ___] := {textCell[ "Wir wissen ", formulaReference[ e], ". Also gilt"], 
	assumptionListCells[ new, ",", ""],
	textCell[ If[ Length[ v] === 1, 
		" f\[UDoubleDot]r ein beliebig aber fixes ", 
		" f\[UDoubleDot]r beliebige aber fixe "
	], inlineTheoremaExpressionSeq[ v, lang], "."]
	};

proofStepText[ existsKB, lang, {{g_}}, {{simpG_}}, ___] := {textCell[ "Die zu beweisende Allaussage ", formulaReference[ g], " vereinfacht zu"],
	goalCell[ simpG, "."]
	};

proofStepText[ expandDef, lang, u_List, g_List, ___, "defCond" -> False, "usedDefs" -> defs_List, ___] := 
	(* u, g, and defs have same length.
	   u is a list of singleton lists, u[[i,1]] are the formulae that are rewritten
	   g is a list of singleton lists, g[[i,1]] are the new formulae
	   defs is an auxliliary list containing lists of definition formulae, namely defs[[i]] are the definitions used when rewriting u[[i,1]] to g[[i,1]].
	   According to the "defCond" -> False, this is the case, where NO CONDITIONS need to be checked.
	*)
	Module[ {stepText = {}, j, repl, suffix},
		(* If the first in u and g are the same, then the goal has not been rewritten *)
		If[ u[[1]] =!= g[[1]],
			repl = defs[[1]];
			suffix = If[ Length[ repl] == 1, "", "en"];
			stepText = { textCell[ "Um ", formulaReference[ u[[1, 1]]], " zu beweisen, reicht es aufgrund der Definition" <> suffix <> " ", 
				formulaReferenceSequence[ repl, lang], " aus zu zeigen"],
				goalCell[ g[[1, 1]], "."]}
		];
		PrependTo[ stepText, textCell[ "Wir expandieren Definitionen:"]];
		(* Each of the remaining is an expansion in the KB. Produce a line of text for each of them *)
		Do[
			repl = defs[[j]];
			suffix = If[ Length[ repl] == 1, "", "en"];
			stepText = Join[ stepText, 
				{textCell[ "Aus ", formulaReference[ u[[j, 1]]], " folgt aufgrund der Definition" <> suffix <> " ", formulaReferenceSequence[ repl, lang]], 
				assumptionCell[ g[[j, 1]]]}],
			{j, 2, Length[ g]}
		];
		stepText
	];

proofStepText[ expandDef, lang, u_, g_, ___, "defCond" -> True, "usedDefs" -> defs_List, ___] := {textCell[ "Wir expandieren Definitionen:"]};

subProofHeader[ expandDef, lang, u_, g_, ___, "defCond" -> True, "usedDefs" -> defs_List, ___, {1}] := 
	Module[ {stepText = {}, j, repl, suffix},
		(* If the first in u and g are the same, then the goal has not been rewritten *)
		If[ u[[1]] =!= g[[1]],
			repl = defs[[1]];
			suffix = If[ Length[ repl] == 1, "", "en"];
			stepText = {textCell[ "Um ", formulaReference[ u[[1, 1]]], " zu beweisen, reicht es aufgrund der Definition" <> suffix <> " ", 
				formulaReferenceSequence[ repl, lang], " aus zu zeigen"],
				goalCell[ g[[1, 1]], "."]}
		];
		(* Each of the remaining is an expansion in the KB. Produce a line of text for each of them *)
		Do[
			repl = defs[[j]];
			suffix = If[ Length[ repl] == 1, "", "en"];
			stepText = Join[ stepText, 
				{textCell[ "Aus ", formulaReference[ u[[j, 1]]], " folgt aufgrund der Definition" <> suffix <> " ", formulaReferenceSequence[ repl, lang]], 
				assumptionCell[ g[[j, 1]]]}],
			{j, 2, Length[ g] - 1} (* the last is the new goal for a condition in the rewrite or True if no condition is there -> we go only to Length-1 *)
		];
		stepText
	];

subProofHeader[ expandDef, lang, u_, {___, {cond_}}, ___, "defCond" -> True, "usedDefs" -> defs_List, ___, {2}] := {
	textCell[ "Um obige Definitionen anwenden zu k\[ODoubleDot]nnen, muss gepr\[UDoubleDot]ft werden"],
	goalCell[ cond, "."]
	};	

(* ::Subsection:: *)
(* F *)

proofStepText[ falseInKB, lang, {{k_}}, {}, pVal_] := {textCell[ "Dieser Teil des Beweises ist somit beendet, da ", formulaReference[ k], 
	" ein Widerspruch in der Wissensbasis ist."]
    };

proofStepText[ forallGoal, lang, {{g_}}, {{newG_}}, ___, "abf" -> v_List, ___] := 
	{textCell[ "Zum Beweis von ", formulaReference[ g], " w\[ADoubleDot]hlen wir ",
		inlineTheoremaExpressionSeq[ v, lang], " beliebig aber fix und beweisen"],
		goalCell[ newG, "."]
		};

proofStepText[ forallGoal, lang, {{g_}}, {{newG_, assum__}}, ___, "abf" -> v_List, ___] := 	{textCell[ "Zum Beweis von ", formulaReference[ g], " w\[ADoubleDot]hlen wir ", 
	inlineTheoremaExpressionSeq[ v, lang], " beliebig aber fix und nehmen an"],
	assumptionListCells[ {assum}, ",", "."],
	textCell[ "Es ist nun zu zeigen"],
	goalCell[ newG, "."]
	};

proofStepText[ forallGoal, lang, {{g_}}, {{simpG_}}, ___] := {textCell[ "Die zu beweisende Allaussage ", formulaReference[ g], " vereinfacht zu"],
	goalCell[ simpG, "."]
	};

proofStepText[ forallKB, lang, {{u_}}, {}, ___] := 
	(* Instantiation has been tried, but was not successful *)
	{textCell[ "Keine Instanzierung von ", formulaReference[ u], " m\[ODoubleDot]glich."]};
	
proofStepText[ forallKB, lang, {{u_}}, {g_}, ___, "instantiation" -> inst_List, ___] :=
    Module[ {instText = {textCell[ "Wir instanzieren ", formulaReference[ u], ":"]}, i},
        Do[
            instText = Join[ instText,
                {textCell[ "Unter Verwendung von ", inlineTheoremaExpression[ inst[[ i]]], " erhalten wir"],
                assumptionCell[ g[[ i]], "."]}],
            {i, Length[ g]}
        ];
        instText
    ];

proofStepText[ forallKBInteractive, lang, {{u_}}, {{g_}}, ___, "instantiation" -> inst_List, ___] :=
	{textCell[ "Aussage ", formulaReference[ u], " gilt insbesondere f\[UDoubleDot] ", inlineTheoremaExpressionSeq[ inst, lang], ", d.h."],
	assumptionCell[ g, "."]
    };

(* ::Subsection:: *)
(* G *)

proofStepText[ goalInKB, lang, {{goal_, k_}}, {}, pVal_] := {textCell[ "Das Beweisziel ", formulaReference[ goal], 
	" stimmt mit der Aussage ", formulaReference[ k], " in der Wissensbasis \[UDoubleDot]berein. Dieser Teil des Beweises ist somit beendet."]
    };

proofStepText[ goalRewriting, lang, {}, {}, ___] := {textCell[ "Keine Umformung des Beweisziels."]};
(* Case: goal rewriting applicable, but no rewrite possible *)	

proofStepText[ goalRewriting, lang, {{origGoal_, rewrittenBy_}}, {{g_}}, ___] := 
(* Case: no condition generated *)
	{textCell[ "Mit Hilfe von ", formulaReference[ rewrittenBy], " reduzieren wir den Beweis von ", formulaReference[ origGoal], " auf den Beweis von "],
	goalCell[ g, "."]};
	
(* ::Subsection:: *)
(* I *)

proofStepText[ implGoalCP, lang, {{g_}}, {{nr_, nl_}}, ___] := {textCell[ "Wir beweisen ", formulaReference[ g], " mit Kontraposition, d.h. wir nehmen an"],
	assumptionCell[ nr],
	textCell[ "und beweisen"],
	goalCell[ nl, "."]
	};

proofStepText[ implGoalDirect, lang, {{g_}}, {{l_, r_}}, ___] := {textCell[ "Um ", formulaReference[ g], " zu beweisen, nehmen wir an"],
	assumptionCell[ l],
	textCell[ "und zeigen"],
	goalCell[ r, "."]
	};

proofStepText[ implicitDef, lang, {}, {}, ___] := {};

proofStepText[ implicitDef, lang, u_, g_, ___, "introConstFor" -> termConst_List, ___] := 
	Module[ {stepText, j},
		stepText = {textCell[ "F\[UDoubleDot]r die implizit definierte Funktion ", formulaReference[ u[[1, 1]]], " f\[UDoubleDot]hren wir neue Konstante ", 
			inlineTheoremaExpressionSeq[ Apply[ EqualDef$TM, termConst, {1}], lang], " ein, sodass"],
			assumptionListCells[ g[[1]], ",", "."]};
		(* g[[2]] is the new goal. {} if no rewrite happened in the goal *)
		If[ g[[2]] =!= {},
			stepText = Join[ stepText,
				{textCell[ "Um Aussage ", formulaReference[ u[[2, 1]]], " zu beweisen, reicht es nun wegen ", formulaReferenceSequence[ Rest[ u[[2]]], lang], " aus zu zeigen, dass"],
				goalCell[ g[[2, 1]], "."]}
			]
		];
		(* Each of the remaining is an expansion in the KB. Produce a line of text for each of them *)
		Do[
			stepText = Join[ stepText, 
				{textCell[ "Die Annahme ", formulaReference[ u[[j, 1]]], " wird aufgrund von ", formulaReferenceSequence[ Rest[ u[[j]]], lang], " zu"], 
				assumptionCell[ g[[j, 1]]]}],
			{j, 3, Length[g]}
		];
		stepText
	];

proofStepText[ implKBCases, lang, {{g_}}, {{_, _}}, ___] := {textCell[ "Basierend auf der Annahme ", formulaReference[ g], " unterscheiden wir zwei F\[ADoubleDot]lle:"]};

subProofHeader[ implKBCases, lang, _, {generated:{_, _}}, ___, pVal_, {p_}] := {textCell[ "Fall ", ToString[ p], ": wir nehmen an"],
	assumptionCell[ Part[ generated, p], "."]
	};

proofStepText[ inequality1, lang, {{g_, k_}}, {}, ___] := 
	{textCell[ "Aufgrund von ", formulaReference[ k], " ist ", formulaReference[ g], " wahr."]};	
		
proofStepText[ instantiate, lang, u_, {}, ___] := 
	(* Instantiation has been tried, but none of them could be successfully applied *)
	{textCell[ "Neue Konstante stehen bereit, es konnte aber keine Instanzierung durchgef\[UDoubleDot]hrt werden."]};
	
proofStepText[ instantiate, lang, u_, g_, ___, "instantiation" -> inst_List, ___] := 
	Module[ {stepText = {textCell[ "Neue Konstante zur Instanzierung stehen bereit."]}, instText = {}, j, i},
		(* Each of the g_i is a list of instances of u_i *)
		Do[
			instText = {textCell[ "Wir instanzieren ", formulaReference[ u[[j, 1]]], ":"]};
			Do[
				instText = Join[ instText,
					{textCell[ "Mit ", inlineTheoremaExpressionSeq[ inst[[j, i]], lang], " erhalten wir"],
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

proofStepText[ knowledgeRewriting, lang, {}, {}, ___] := {textCell[ "Keine Umformungen in der Wissensbasis."]};
(* Case: knowledge rewriting applicable, but no rewrite possible *)	

proofStepText[ knowledgeRewriting, lang, u_, g_, ___] := 
(* Case: new knowledge generated *)
    Module[ {stepText = {textCell["Wir erweitern unser Wissen:"]}, j},
        Do[
            stepText = Append[ stepText, 
            	cellGroup[ {textCell[ "Aus ", formulaReference[ u[[j, 1]]], " kann mittels ", formulaReferenceSequence[ Rest[ u[[j]]], lang], " hergeleitet werden"],
            		assumptionListCells[ g[[j]], ",", "."]}]],
            {j, Length[ g]}
        ];
        stepText
    ];

(* ::Subsection:: *)
(* M *)

proofStepText[ maxTuples1, lang, {{g_}}, {}, ___, "comp" -> {t1_, t2_, e_, m_}, ___] := 
	{textCell[ "Das Tupel ", inlineTheoremaExpression[ t1], 
		" enth\[ADoubleDot]lt die gleichen Elemente wie ", inlineTheoremaExpression[ t2], ", und eines zus\[ADoubleDot]tzlich, n\[ADoubleDot]mlich ",
		inlineTheoremaExpression[ e], ". Daher ist ", inlineTheoremaExpression[ m], 
		", womit ", formulaReference[ g], " bewiesen ist."]};
	
proofStepText[ multipleGoalRewriting, lang, ___] := {textCell[ "Das Beweisziel kann auf verschiedene Arten umgeformt werden."]};

subProofHeader[ multipleGoalRewriting, lang, u_, g_, ___, pVal_, {p_}] := {};

(* ::Subsection:: *)
(* N *)

proofStepText[ notGoal|contradiction, lang, {{g_}}, {{opp_}}, ___] := {textCell[ "Widerspruchsbeweis von ", formulaReference[ g], ". Wir nehmen an"],
	assumptionCell[ opp],
	textCell[ "und f\[UDoubleDot]hren dies auf einen Widerspruch."]
	};

(* ::Subsection:: *)
(* O *)

proofStepText[ orGoal, lang, {{g_}}, {{negAssum__, newG_}}, ___] := {textCell[ "Um die Disjunktion ", formulaReference[ g], " zu beweisen, nehmen wir an"],
	assumptionListCells[ {negAssum}, ",", ""],
	textCell[ "und zeigen schlussendlich"],
	goalCell[ newG, "."]
	};

proofStepText[ orKB, lang, {{g_}}, {generated_List}, ___] := {textCell[ "Aufgrund von ", formulaReference[ g], " kann eine Fallunterscheidung gemacht werden:"]};

subProofHeader[ orKB, lang, _, {generated_List}, ___, pVal_, {p_}] := {textCell[ "Fall ", ToString[p], ": Wir nehmen an"],
	assumptionCell[ Part[ generated, p], "."]
	};

(* ::Subsection:: *)
(* P *)

proofStepText[ partSolveMetaMatching, lang, {{u_}}, {{g_}}, ___, "instantiation" -> inst_List, ___] := {
	textCell[ "Sei nun ", inlineTheoremaExpressionSeq[ inst[[ 1]], lang], ". Um die Aussage ", formulaReference[ u], " zu beweisen, zeigen wir nun"],
	goalCell[ g, "."]
	};

(* ::Subsection:: *)
(* S *)

proofStepText[ solveMetaUnification, lang, {{u_}}, {{g_}}, ___, "instantiation" -> inst_List, ___] := {
	textCell[ "Sei nun ", inlineTheoremaExpressionSeq[ inst[[ 1]], lang], ". Um die Aussage ", formulaReference[ u], " zu beweisen, zeigen wir nun"],
	goalCell[ g, "."]
	};

proofStepText[ solveMetaUnification, lang, {{u_}}, {g_List}, ___, "instantiation" -> inst_List, ___] := 
	{textCell[ "Man kann Werte f\[UDoubleDot]r die zu bestimmenden Variablen einsetzen."]};

subProofHeader[ solveMetaUnification, lang, {{u_}}, {g_List}, ___, "instantiation" -> inst_List, ___, {i_}] := {
	textCell[ "Sei nun ", inlineTheoremaExpressionSeq[ inst[[i]], lang], ". Um die Aussage ", formulaReference[ u], " zu beweisen, zeigen wir nun"],
	goalCell[ g[[i]], "."]
	};	

(* ::Subsection:: *)
(* T *)

proofStepText[ trueGoal, lang, {{goal_}}, {}, pVal_] := {textCell[ "Der Beweis ist zu Ende, da das Beweisziel ", formulaReference[ goal], 
	" wahr ist."]
    };


(* UNTRANSLATED *)
	
		
] (* With *)

End[]
