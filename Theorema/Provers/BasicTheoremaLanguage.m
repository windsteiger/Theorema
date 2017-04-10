(* Theorema 
    Copyright (C) 2010 The Theorema Group

    This file is part of Theorema 2.0
    
    Theorema 2.0 is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Theorema 2.0 is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*)

BeginPackage[ "Theorema`Provers`BasicTheoremaLanguage`"]

Needs[ "Theorema`Provers`"]
Needs[ "Theorema`Common`"]
Needs[ "Theorema`Language`"]

Begin["`Private`"]


(* ::Section:: *)
(* Termination rules *)

(*
	Termination rules are NOT applied with ReplaceList but just with Replace (efficiency!)
	We cannot use the trick with returning $Failed to indicate non-applicability.
*)
inferenceRule[ goalInKB] = 
PRFSIT$[ goal:FML$[ _, g_, __], {___, k:FML$[ _, g_, __], ___}, ___] :> performProofStep[
	makeTERMINALNODE[ makePRFINFO[ name -> goalInKB, used -> {goal, k}], proved]
]

inferenceRule[ contradictionKB] = 
PRFSIT$[ goal_FML$, {___, k:FML$[ _, phi_, __], ___, c:FML$[ _, Not$TM[ phi_], __], ___} | {___, k:FML$[ _, Not$TM[ phi_], __], ___, c:FML$[ _, phi_, __], ___}, ___] :> performProofStep[
	makeTERMINALNODE[ makePRFINFO[ name -> contradictionKB, used -> {k, c}], proved]
]

inferenceRule[ falseInKB] =
PRFSIT$[ goal_FML$, {___, k:FML$[ _, False | Not$TM[ True], __], ___}, ___] :> performProofStep[
	makeTERMINALNODE[ makePRFINFO[ name -> falseInKB, used -> k], proved]
]

inferenceRule[ trueGoal] =
PRFSIT$[ goal:FML$[ _, True | Not$TM[ False], __], _List, ___] :> performProofStep[
	makeTERMINALNODE[ makePRFINFO[ name -> trueGoal, used -> goal], proved]
]

inferenceRule[ contradictionUniv1] = 
(PRFSIT$[ _, {___, c:FML$[ _, Not$TM[ B_?isAtomicExpression], _], ___, u:FML$[ _, Forall$TM[ _, _, A_?isAtomicExpression], _], ___}, _, ___?OptionQ]|
PRFSIT$[ _, {___, u:FML$[ _, Forall$TM[ _, _, A_?isAtomicExpression], _], ___, c:FML$[ _, Not$TM[ B_?isAtomicExpression], _], ___}, _, ___?OptionQ]|
PRFSIT$[ _, {___, c:FML$[ _, B_?isAtomicExpression, _], ___, u:FML$[ _, Forall$TM[ _, _, Not$TM[ A_?isAtomicExpression]], _], ___}, _, ___?OptionQ]|
PRFSIT$[ _, {___, u:FML$[ _, Forall$TM[ _, _, Not$TM[ A_?isAtomicExpression]], _], ___,  c:FML$[ _, B_?isAtomicExpression, _], ___}, _, ___?OptionQ]) :> 
	Module[ {inst},
		Block[ {$generated = {}},
			makeTERMINALNODE[ makePRFINFO[ name -> contradictionUniv1, used -> {u, c}, 
				"instantiation" -> inst], proved]
		] /; (inst = instantiation[ A, B]) =!= $Failed
	]

inferenceRule[ contradictionUniv2] = 
(PRFSIT$[ _, {___, c:FML$[ _, Forall$TM[ _, _, Not$TM[ B_?isAtomicExpression]], _], ___, u:FML$[ _, Forall$TM[ _, _, A_?isAtomicExpression], _], ___}, _, ___?OptionQ]|
PRFSIT$[ _, {___, u:FML$[ _, Forall$TM[ _, _, A_?isAtomicExpression], _], ___, c:FML$[ _, Forall$TM[ _, _, Not$TM[ B_?isAtomicExpression]], _], ___}, _, ___?OptionQ]) :> 
	Module[ {com, inst, pos},
		Block[ {$generated = {}},
			makeTERMINALNODE[ makePRFINFO[ name -> contradictionUniv2, used -> {u, c}, 
				"instantiation" -> Extract[ inst, pos[[1]]]], proved]
		] /; ({com, inst} = unification[ A, B]) =!= {$Failed, $Failed} && (pos = Position[ com, _?(freeVariables[ #] === {}&), {1}, Heads -> False]) =!= {}
]

	
(* ::Section:: *)
(* Connectives *)

(* ::Subsection:: *)
(* NOT *)

inferenceRule[ notGoal] = 
PRFSIT$[ g:FML$[ _, Not$TM[ a_], __], k_List, id_, rest___?OptionQ] :> performProofStep[
	Module[ {opp},
		opp = makeAssumptionFML[ formula -> a];
		makeANDNODE[ makePRFINFO[ name -> notGoal, used -> g], 
			toBeProved[ goal -> makeFML[ formula -> False, label -> "\[UpTee]"], kb -> prependKB[ k, opp], rest]
		]
	]
]

inferenceRule[ contradiction] = 
PRFSIT$[ g:FML$[ _, a_, __] /; !TrueQ[ !a] && FreeQ[ g, _META$], k_List, id_, rest___?OptionQ] :> performProofStep[
	Module[ {opp},
		opp = makeAssumptionFML[ formula -> Not$TM[ a]];
		makeANDNODE[ makePRFINFO[ name -> contradiction, used -> g], 
			toBeProved[ goal -> makeFML[ formula -> False, label -> "\[UpTee]"], kb -> prependKB[ k, opp], rest]
		]
	]
]

inferenceRule[ deMorganKB] = 
PRFSIT$[ g_, k_List, id_, rest___?OptionQ] :> performProofStep[
	Module[ {newKB, changed},
		newKB = Map[ applyDeMorgan[ #1, makeAssumptionFML]&, k];
		changed = Cases[ newKB, {new_, False, orig_} -> {new, orig}];
		If[ changed === {},
			Throw[ $Failed]
		];
		makeANDNODE[ makePRFINFO[ name -> deMorganKB, used -> Map[ Drop[ #, 1]&, changed],
			generated -> Map[ Drop[ #, -1]&, changed]], 
			toBeProved[ goal -> g, kb -> Map[ Part[ #, 1]&, newKB], rest]
		]
	]
]

applyDeMorgan[ orig:FML$[ _, fml_, __], mkFml_] :=
Module[
	{
		deMorgan = {Not$TM[ And$TM[ x_, y__]] :> Map[ Not$TM, Or$TM[ x, y]],
		Not$TM[ Or$TM[ x_, y__]] :> Map[ Not$TM, And$TM[ x, y]],
		Not$TM[ Implies$TM[ x_, y_]] :> And$TM[ x, Not$TM[y]],
		Not$TM[ Iff$TM[ x_, y_]] :> Or$TM[ And$TM[ x, Not$TM[y]], And$TM[ y, Not$TM[x]]],
		Not$TM[ Forall$TM[ r_, c_, f_]] :> Exists$TM[ r, c, Not$TM[f]],
		Not$TM[ Exists$TM[ r_, c_, f_]] :> Forall$TM[ r, c, Not$TM[f]]}
	},
	With[ {dm = fml //. deMorgan},
		{mkFml[ formula -> dm], fml === dm, orig}
	]
]
	
(* ::Subsection:: *)
(* AND *)

inferenceRule[ andGoal] = 
PRFSIT$[ g:FML$[ _, And$TM[ c__], lab_, ___] /; FreeQ[ {c}, _META$], k_List, id_, rest___?OptionQ] :> performProofStep[
	Module[ {conj},
		conj = MapIndexed[ makeGoalFML[ formula -> #1, label -> lab <> "." <> ToString[ #2[[1]]]]&, {c}];
		makeANDNODE[ makePRFINFO[ name -> andGoal, used -> g], 
			Map[ toBeProved[ goal -> #, kb -> k, rest]&, conj]
		]
	]
]

inferenceRule[ andKB] = 
PRFSIT$[ g_, {pre___, k:FML$[ _, And$TM[ c__], lab_, ___], post___}, id_, rest___?OptionQ] :> performProofStep[
	Module[ {conj},
		conj = MapIndexed[ makeAssumptionFML[ formula -> #1, label -> lab <> "." <> ToString[ #2[[1]]]]&, {c}];
		makeANDNODE[ makePRFINFO[ name -> andKB, used -> k], 
			toBeProved[ goal -> g, kb -> joinKB[ conj, {pre, post}], rest]
		]
	]
]


(* ::Subsection:: *)
(* OR *)

inferenceRule[ orGoal] = 
PRFSIT$[ g:FML$[ _, Or$TM[ a__, b_], lab_, ___] /; FreeQ[ {a, b}, _META$], k_List, id_, rest___?OptionQ] :> performProofStep[
	Module[ {negAssum, newG},
		negAssum = MapIndexed[ makeAssumptionFML[ formula -> Not$TM[#1], label -> lab <> "." <> ToString[ #2[[1]]]]&, {a}];
		newG = makeGoalFML[ formula -> b];
		makeANDNODE[ makePRFINFO[ name -> orGoal, used -> g], 
			toBeProved[ goal -> newG, kb -> joinKB[ negAssum, k], rest]
		]
	]
]

inferenceRule[ orKB] = 
PRFSIT$[ g_, {pre___, k:FML$[ _, Or$TM[ c__], lab_, ___], post___}, id_, rest___?OptionQ] :> performProofStep[
	Module[ {caseAssum},
		caseAssum = MapIndexed[ makeAssumptionFML[ formula -> #1, label -> lab <> "." <> ToString[ #2[[1]]]]&, {c}];
		makeANDNODE[ makePRFINFO[ name -> orKB, used -> k], 
			Map[ Block[ {$rewriteRules = {}}, toBeProved[ goal -> g, kb -> prependKB[{pre, post}, #], rest]]&, caseAssum]
		]
	]
]


(* ::Subsection:: *)
(* IMPLIES *)

inferenceRule[ implGoalDirect] = 
PRFSIT$[ g:FML$[ _, Implies$TM[ P_, Q_], __], k_List, id_, rest___?OptionQ] :> performProofStep[
	Module[ {left, right},
		left = makeAssumptionFML[ formula -> P];
		right = makeGoalFML[ formula -> Q];
		makeANDNODE[ makePRFINFO[ name -> implGoalDirect, used -> g], 
			toBeProved[ goal -> right, kb -> prependKB[ k, left], rest]]
	]
]

inferenceRule[ implGoalCP] = 
PRFSIT$[ g:FML$[ _, Implies$TM[ P_, Q_], __], k_List, id_, rest___?OptionQ] :> performProofStep[
	Module[ {negLeft, negRight},
		negRight = makeAssumptionFML[ formula -> Not$TM[ Q]];
		negLeft = makeGoalFML[ formula -> Not$TM[ P]];
		makeANDNODE[ makePRFINFO[ name -> implGoalCP, used -> g], 
			toBeProved[ goal -> negLeft, kb -> prependKB[ k, negRight], rest]]
	]
]

(*
Modus Ponens is superseded by the much more general rewriting technique, hence, by default it will be deactivated.
*)

inferenceRule[ implKBCases] = 
PRFSIT$[ g_, {pre___, k:FML$[ _, Implies$TM[ l_?isAtomicExpression, r_?isAtomicExpression], lab_, ___], post___}, id_, rest___?OptionQ] :> performProofStep[
	Module[ {case1, case2},
		case1 = makeAssumptionFML[ formula -> Not$TM[ l], label -> lab <> ".1"];
		case2 = makeAssumptionFML[ formula -> r, label -> lab <> ".2"];
		makeANDNODE[ makePRFINFO[ name -> implKBCases, used -> k], 
			{toBeProved[ goal -> g, kb -> prependKB[ {pre, post}, case1], rest],
			 toBeProved[ goal -> g, kb -> prependKB[ {pre, post}, case2], rest]}
		]
	]
]


(* ::Subsection:: *)
(* IFF *)

inferenceRule[ equivGoal] = 
PRFSIT$[ g:FML$[ _, Iff$TM[ P_, Q_], __], k_List, id_, rest___?OptionQ] :> performProofStep[
	Module[ {left2right, right2left},
		left2right = makeGoalFML[ formula -> Implies$TM[ P, Q]];
		right2left = makeGoalFML[ formula -> Implies$TM[ Q, P]];
		makeANDNODE[ makePRFINFO[ name -> equivGoal, used -> g], 
			{toBeProved[ goal -> left2right, kb -> k, rest],
			toBeProved[ goal -> right2left, kb -> k, rest]}
		]
	]
]

(* ::Section:: *)
(* Quantifiers *)

(* ::Subsection:: *)
(* FORALL *)

inferenceRule[ forallGoal] =
ps:PRFSIT$[ g:FML$[ _, u:Forall$TM[ _, _, _], __], k_List, id_, rest___?OptionQ] :> performProofStep[
	Module[ {faBui, simp, rc, r, c, f, fix, newConds, newGoal, locC},
		(* we use computation regardless whether it is activated or not ... *)
		faBui = buiActProve[ "Forall"];
		buiActProve[ "Forall"] = True;
		simp = computeInProof[ standardFormQuantifier[ u]];
		buiActProve[ "Forall"] = faBui;
		If[ MatchQ[ simp, Forall$TM[ _, _, _]],
			(* no simplification *)
			(* note: because of 'standardFormQuantifier' we have to extract 'rng', 'cond' and 'A' from 'simp', not from 'u'! *)
			With[ {rng = First[ simp], cond = simp[[2]], A = Last[ simp]},
				rc = rngToCondition[ rng];
				If[ !FreeQ[ rc, $Failed],
					$Failed,
					(* else *)
					{{r, c, f}, fix} = arbitraryButFixed[ {rc, cond, A}, rng, {g, k}];
					locC = getOptionalComponent[ ps, "constants"];
					newGoal = makeGoalFML[ formula -> f];
					newConds = Map[ makeAssumptionFML[ formula -> #]&, DeleteCases[ Append[ r, c], True]];
					makeANDNODE[ makePRFINFO[ name -> forallGoal, used -> g, "abf" -> rngConstants[ fix]],
						toBeProved[ goal -> newGoal, kb -> joinKB[ newConds, k], "constants" -> Prepend[ locC, fix], rest]]
				]
			],
			(* else *)
			simp = makeGoalFML[ formula -> simp];
			makeANDNODE[ makePRFINFO[ name -> forallGoal, used -> g],
				toBeProved[ goal -> simp, kb -> k, rest]]
		]
	]
]

inferenceRule[ forallKB] =
ps:PRFSIT$[ g_, K:{___, u:FML$[ fk_, f_Forall$TM, r__], ___}, id_, rest___?OptionQ] :> performProofStep[
	Module[ {faInst, newConst, oldConst, inst},
	    faInst = getOptionalComponent[ ps, "forallKB"];
	    If[ MemberQ[ faInst, fk],
                (* Rule forallKB has already been applied for those forms *)
	        Throw[ $Failed]
	    ];
	    {newConst, oldConst} = constants[ ps];
        (* we instantiate with the "old" constants only, because the new ones will be treated by the 'instantiate'-rule separately *)
	    inst = instantiateForall[ FML$[ fk, standardFormQuantifier[ f], r], Apply[ RNG$, oldConst]];
	    makeANDNODE[ makePRFINFO[ name -> forallKB, used -> u, "instantiation" -> inst[[2]]], 
	        toBeProved[ goal -> g, kb -> joinKB[ inst[[1]], K], "forallKB" -> Prepend[ faInst, fk], rest]]
	]
]

inferenceRule[ forallKBInteractive] =
ps:PRFSIT$[ g_, K:{___, f:FML$[ _, Forall$TM[ _, _, _], __], ___}, id_, rest___?OptionQ] :> performProofStep[
    Module[ {simp = standardFormQuantifier[ f], rc, r, c, Ainst, fInst, inst},
    	If[ MatchQ[ simp, Forall$TM[ _, _, _]],
	    	With[ {rng = First[ simp], cond = simp[[2]], A = Last[ simp]},
		        rc = rngToCondition[ rng];
		        If[ !FreeQ[ rc, $Failed],
		            $Failed,
		            (* else *)
		            {{r, c, Ainst}, inst} = instantiateUnivKnowInteractive[ {rc, cond, A}, rng, {g, K}];
		            If[ inst === $Failed,
		            	(* interactive dialog has been canceled *)
		                $Failed,
		                (* else *)
		                fInst = makeAssumptionFML[ formula -> Implies$TM[ And$TM[ r, c], Ainst]];
		                makeANDNODE[ makePRFINFO[ name -> forallKBInteractive, used -> f, "instantiation" -> inst],
		                    toBeProved[ goal -> g, kb -> prependKB[ K, fInst], rest]]
		            ]
		        ]
	    	],
	    (*else*)
	    	$Failed
    	]
    ]
]

(* ::Subsection:: *)
(* EXITSTS *)

inferenceRule[ existsGoal] = 
PRFSIT$[ g:FML$[ _, u:Exists$TM[ rng_, cond_, A_], __], k_List, id_, rest___?OptionQ] :> performProofStep[
	Module[ {simp, rc, r, c, f, meta, newGoal},
		simp = computeInProof[ u];
		If[ MatchQ[ simp, _Exists$TM],
			(* no simplification *)
			rc = rngToCondition[ rng];
			If[ !FreeQ[ rc, $Failed], 
				$Failed,
				(* else *)
				{{r, c, f}, meta} = introduceMeta[ {rc, cond, A}, rng, {g, k}];
				newGoal = makeGoalFML[ formula -> Apply[ And$TM, DeleteCases[ Join[ r, {c, f}], True]]];
				makeANDNODE[ makePRFINFO[ name -> existsGoal, used -> g, "meta" -> meta], 
					toBeProved[ goal -> newGoal, kb -> k, rest]]

			],
			(* else: quantifier simplified *)
			simp = makeGoalFML[ formula -> simp];
			makeANDNODE[ makePRFINFO[ name -> existsGoal, used -> g], 
				toBeProved[ goal -> simp, kb -> k, rest]]
		]
	]
]
	
inferenceRule[ existsGoalInteractive] = 
ps:PRFSIT$[ g:FML$[ _, u:Exists$TM[ rng_, cond_, A_], __], k_List, id_, rest___?OptionQ] :> performProofStep[
    Module[ {const, subst, rc, instRng, thinnedRng, newGoal},
    	const = getAllConstants[ ps];
        subst = instantiateExistGoalInteractive[ g, const, k];
        If[ subst === $Failed,
        	(* the interactive dialog has been canceled or closed *)
            $Failed,
            (* else *)
            instRng = Select[ rng, MemberQ[ Map[ First, subst], First[#]]&];
			thinnedRng = Complement[ rng, instRng];
            rc = rngToCondition[ instRng];
            If[ !FreeQ[ rc, $Failed], 
				$Failed,
				(* else *)
				newGoal = makeExist[ thinnedRng, rc, cond, A, subst];
				If[ newGoal === $Failed,
					$Failed,
				(*else*)
	            	newGoal = makeGoalFML[ formula -> newGoal];
	            	makeANDNODE[ makePRFINFO[ name -> existsGoalInteractive, used -> g, "instantiation" -> subst], 
	                	toBeProved[ goal -> newGoal, kb -> k, rest]]
				]
            ]
        ]
    ]
]

makeExist[ RNG$[], cond1_List, cond2_, A_, subst_] :=
	With[ {res = substituteFree[ DeleteCases[ Join[ cond1, {cond2, A}], True], subst]},
		If[ res === $Failed,
			$Failed,
			And$TM @@ res
		]
	]
makeExist[ r:RNG$[__], cond1_List, cond2_, A_, subst_] :=
	With[ {res = substituteFree[ DeleteCases[ Join[ cond1, {cond2, A}], True], subst]},
		If[ res === $Failed,
			$Failed,
			Exists$TM[ r, True, And$TM @@ res]
		]
	]
makeExist[ args___] := unexpected[ makeExist, {args}]

  
inferenceRule[ existsKB] = 
ps:PRFSIT$[ g_, k:{pre___, e:FML$[ _, u:Exists$TM[ rng_, cond_, A_], __], post___}, id_, rest___?OptionQ] :> performProofStep[
	Module[ {simp, r, c, f, fix, newConds, locC},
		simp = computeInProof[ u];
		If[ MatchQ[ simp, _Exists$TM],
			(* no simplification *)
			{{r, c, f}, fix} = arbitraryButFixed[ {rngToCondition[ rng], cond, A}, rng, {g, k}];
			locC = Prepend[ getOptionalComponent[ ps, "constants"], fix];
			newConds = Map[ makeAssumptionFML[ formula -> #]&, DeleteCases[ Join[ r, {c, f}], True]];
			makeANDNODE[ makePRFINFO[ name -> existsKB, used -> e, "abf" -> rngConstants[ fix]], 
				toBeProved[ goal -> g, kb -> joinKB[ newConds, {pre, post}], "constants" -> locC, rest]],
			(* else *)
			simp = makeAssumptionFML[ formula -> simp];
			makeANDNODE[ makePRFINFO[ name -> existsKB, used -> e], 
				toBeProved[ goal -> g, kb -> prependKB[ {pre, post}, simp], rest]]
		]
	]
]


(* ::Section:: *)
(* goal rewriting *)

(*
	In the proof situations "goalRewriting"-> we store {g, {key1, ..., keyn}}, where
	g is the key of the goal and
	keyi are the keys of the rewrite rules
	that were available when the rule was applied to g.
	
	The idea is that if we try to rewrite a goal G, then we look what happened at the last rewrite: say {g, {key1, ..., keyn}}.
	If G != g then use all rules available in goalRules, otherwise use just "new" goalRules. If there are no new rules then stop,
	otherwise rewrite. If none of the new rules apply, then do a proof step that documents which rules have already been tried.
	Otherwise generate one new goal or an alternative of several new goals.
*)
inferenceRule[ goalRewriting] = 
this:PRFSIT$[ g:FML$[ _, _?isLiteralExpression, __], k_List, id_, rest___?OptionQ] :> performProofStep[
	Module[ {lastGoalRewriting, rules, usedSubsts, conds, newForms, newG, j, newNodes = {}},
		lastGoalRewriting = getOptionalComponent[ this, "goalRewriting"];
		If[
			(* first application of this rule or applied to new goal *)
			lastGoalRewriting === {} || key@g =!= lastGoalRewriting[[1]],
			rules = goalRules@this,
			(* else: applied to this goal aleady before, we only consider the new rules *)
			rules = DeleteCases[ goalRules@this, {Apply[ Alternatives, lastGoalRewriting[[2]]], _}]
			(* if there are no new rules, then rules={} *)
		];
			
		If[ rules === {},
			(* There are no (new) rules available -> stop *)
			$Failed,
			(* else: we have new rules *)
			{newForms, usedSubsts, conds} = replaceListAndTrack[ formula@g, filterRules[ rules, key@g]];
			Do[
				newG = makeGoalFML[ formula -> newForms[[j]]];
				(* Goal rewriting should actually generate NO conditions. If a condition still appears, there must have gone something wrong *)
				Assert[ conds[[j]]];
				(* The second param to "goalRewriting" -> is unimportant, because there is a new goal, so we will not access it when the rule is applied next time.*)
				(* We have to explicitly specify generated-> because otherwise each node would get all the formulas generated up to then *)
				AppendTo[ newNodes, 
					makeANDNODE[ makePRFINFO[ name -> goalRewriting, used -> Prepend[ usedSubsts[[j]], g], generated -> newG], 
						toBeProved[ goal -> newG, kb -> k, goalRules -> filterRules[ goalRules@this, Map[ key, usedSubsts[[j]]]], "goalRewriting" -> {key@g, {}}, rest]]],
				{j, Length[ newForms]}
			];
			Switch[ Length[ newNodes],
				0,
				makeANDNODE[ makePRFINFO[ name -> goalRewriting, used -> {}], 
						toBeProved[ goal -> g, kb -> k, "goalRewriting" -> {key@g, Map[ First, goalRules@this]}, rest]],
				1,
				First[ newNodes],
				_,
				makeORNODE[ 
					makePRFINFO[ name -> multipleGoalRewriting, used -> used@newNodes, generated -> generated@newNodes],
					newNodes]
			]            	
		]
	]
]

(* ::Section:: *)
(* Knowledge Rewriting *)
(*
	In the proof situations "KBRewriting"-> we store {{k1, {key1, ..., keyn}}, ...,{km, {key1, ..., keyn}}}, where
	kj is the key of the j-th kb entry and
	keyi are the keys of the rewrite rules that were available when the rule was applied to kj.
	
	The idea is that if we try to rewrite kj, then we look what happened at the last rewrite: say {kj, {key1, ..., keyn}}.
	If kj has not yet been rewritten then use all rules available in kbRules, otherwise use just "new" kbRules. If there are no new rules then continue with kj+1,
	otherwise rewrite. Do a proof step that documents which rules have already been tried at which kj.
*)

inferenceRule[ knowledgeRewriting] = 
this:PRFSIT$[ g_FML$, k_List, id_, rest___?OptionQ] :> performProofStep[
	Module[ {rules, auxKB, lastKBRewriting, rewritable, lastKjRewriting, usedSubsts, conds, newForms, newKB = {}, usedForRW = {}, 
			j, i, thisKBRewriting = {}, pos},
		If[ kbRules@this === {},
			Throw[ $Failed]
		];
		auxKB = getOptionalComponent[ this, "AuxiliaryKB"];
		lastKBRewriting = getOptionalComponent[ this, "KBRewriting"];
		rewritable = Cases[ k, FML$[ _, _?isLiteralExpression, __]];
		(* try to rewrite each atomic formula individually *)
		Do[
			lastKjRewriting = Cases[ lastKBRewriting, {key@rewritable[[j]], rkj_} -> rkj];
			If[ lastKjRewriting === {},
				(* if kj has not been rewritten yet, use all rewrite rules *)
				rules = kbRules@this,
				(* else: use only new ones *)
				(* lastKjRewriting must have length 1, we can safely access just the one element *)
				lastKjRewriting = lastKjRewriting[[1]];
				rules = DeleteCases[ kbRules@this, {Apply[ Alternatives, lastKjRewriting], _}];
				If[ rules === {},
					(* In this case, no new rules are there compared to those that applied already *)
					AppendTo[ thisKBRewriting, {key@rewritable[[j]], lastKjRewriting}];
					Continue[];
				]
			];
			(* there are potential rules for kj *)
			(* do not use a rule derived from kj to kj itself *)
			{newForms, usedSubsts, conds} = replaceListAndTrack[ formula@rewritable[[j]], filterRules[ rules, key@rewritable[[j]]]];
			(* record the rules already tried for this formula, these will not be tried again on the same formula *)
			lastKjRewriting = Join[ lastKjRewriting, DeleteCases[ DeleteDuplicates[ Map[ First, rules]], key@rewritable[[j]]]];
			(* walk through newForms and join them to the newKB *)
			Do[
				pos = {};
				If[ TrueQ[ conds[[i]]] || !MemberQ[ pos = posInKB[ Map[ formula, Join[ k, auxKB]], conds[[i]]], {}],
					(* conditions are True or all fulfilled in k *)
					AppendTo[ newKB, {makeAssumptionFML[ formula -> newForms[[i]]]}];
					(* pos contains a list of positions of plain formulas in the list of plain formulas. 
					   When we extract exactly these positions from the whole KB we get the whole formula datastructures *)
					AppendTo[ usedForRW, Prepend[ Join[ usedSubsts[[i]], Extract[ Join[ k, auxKB], Flatten[ pos, 1]]], rewritable[[j]]]],
					(* else *)
					(* the conditions were not fulfilled, we try the rules again next time, because conditions may be fulfilled then *)
					lastKjRewriting = Complement[ lastKjRewriting, Map[ key, usedSubsts[[i]]]];
				],
				{i, Length[ newForms]}
			];
			(* thisKBRewriting contains for each rewritable formula a list of keys of formulas that have already been tried for rewriting.
				In the next run, we do not use these rules again. *)
			AppendTo[ thisKBRewriting, {key@rewritable[[j]], lastKjRewriting}], 
			{j, Length[ rewritable]}
		];
		If[ ValueQ[ newForms],
			(* this means that at least one formula has been tried to rewrite with new formulas. We document this in the proof object *)
			makeANDNODE[ makePRFINFO[ name -> knowledgeRewriting, used -> usedForRW, generated -> newKB], 
				toBeProved[ goal -> g, kb -> joinKB[ Flatten[ newKB], k], "KBRewriting" -> thisKBRewriting, rest]],
			(* this means we exited the outer loop always through the Continue[], i.e. there were no new rewrite rules available ->
				the rule should not apply *)
			Throw[ $Failed]
		]
	]
]

posInKB[ kb_List, And$TM[ f__]] := Map[ Position[ kb, #, {1}]&, {f}]
posInKB[ kb_List, f_] := Map[ Position[ kb, #, {1}]&, {f}]
posInKB[ args___] := unexpected[ posInKB, {args}]
	
(* ::Section:: *)
(* substitution *)

(* We should generate rules in both directions for equalities. As soon as one is applied, remove the other one. *)
inferenceRule[ elementarySubstitution] = 
this:PRFSIT$[ g_, k_List, id_, rest___?OptionQ] :> performProofStep[
	Module[ {rules, usedSubst, cond, newForm, newG, substCond = {}, usedInCond = {}, newK = {}, substApplied = False, j, usedForms = {}, genForms = {}, replBy = {}, gr = True},
		rules = substRules@this;
		If[ rules === {},
			(* There are no substitutions available -> rule does not apply *)
			$Failed,
			(* else: we have substitutions *)
			{newForm, usedSubst, cond} = replaceRepeatedAndTrack[ formula@g, filterRules[ rules, None]];
			If[ usedSubst =!= {},
				(* rewrite applied *)
				newG = makeGoalFML[ formula -> newForm];
				If[ !TrueQ[ cond],
					AppendTo[ substCond, cond];
					AppendTo[ usedInCond, g]
				];
				With[ {used = DeleteDuplicates[ usedSubst]},
					AppendTo[ usedForms, Prepend[ used, g]];
					AppendTo[ replBy, used]
				];
				AppendTo[ genForms, {newG}];
				substApplied = True,
				(* else: no subst in goal *)
				newG = g;
				gr = False
			];
			Do[
                {newForm, usedSubst, cond} = replaceRepeatedAndTrack[ formula@k[[j]], filterRules[ rules, key@k[[j]]]];
                If[ usedSubst =!= {},
                    (* rewrite applied *)
                    newForm = makeAssumptionFML[ formula -> newForm];
                    If[ !TrueQ[ cond],
						AppendTo[ substCond, cond];
						AppendTo[ usedInCond, k[[j]]]
					];
                    appendToKB[ newK, newForm];
                    With[ {used = DeleteDuplicates[ usedSubst]},
                    	AppendTo[ usedForms, Prepend[ used, k[[j]]]];
						AppendTo[ replBy, used]
                    ];
                    AppendTo[ genForms, {newForm}];
                    substApplied = True,
                    (* else: no subst in this formula *)
                    Block[ {$autoGenerateRules = False}, appendToKB[ newK, k[[j]]]] (* rewrite rules from this formula are already there *)
                ],
                {j, Length[ k]}
            ];
            (* Proof goals for checking the conditions are still missing *)
            If[ substApplied,
            	(* We have to explicitly specify generated-> because we need the proper nesting *)
            	makeANDNODE[ makePRFINFO[ name -> elementarySubstitution, used -> usedForms, generated -> genForms, "goalRewrite" -> gr, "usedSubst" -> replBy], 
					toBeProved[ goal -> newG, kb -> newK, substRules -> DeleteCases[ rules, {_, _FIX$ :> _}], rest]],
				$Failed
            ]
		]
	]
]

(* ::Section:: *)
(* Expand Definitions *)

inferenceRule[ expandDef] = 
this:PRFSIT$[ g_, k_List, id_, rest___?OptionQ] :> performProofStep[
	Module[ {rules, auxKB, usedDefs, cond, new, newG, newForm, newK = {}, defExpand = False, defCond = {}, usedInCond = {}, j, usedForms, genForms, replBy = {}, newGoals},
		rules = defRules@this;
		auxKB = getOptionalComponent[ this, "AuxiliaryKB"];
		If[ rules === {},
			(* There are no definitions available at all in this proof -> expanding defs does not apply *)
			$Failed,
			(* else: we have definition rewrite rules *)
			{new, usedDefs, cond} = replaceAllAndTrack[ formula@g, filterRules[ rules, None]];
			If[ usedDefs =!= {} && freeVariables[ cond] === {},
				(* rewrite applied *)
				(* in this case, the result is of the form {newForm, cond}, where cond are conditions to be fulfilled in order to allow the rewrite *)
				newG = makeGoalFML[ formula -> new];
				If[ !TrueQ[ cond],
					AppendTo[ defCond, cond];
					AppendTo[ usedInCond, g]
				];
				defExpand = True,
				(* else: no def expansion in goal *)
				newG = g
			];
			(* The first used and generated are old/new goal. If they are identical, then the proof header won't print any text for the goal part *)
			genForms = {{newG}};
			With[ {defs = Union[ usedDefs]},
				usedForms = {Prepend[ defs, g]};
				AppendTo[ replBy, defs]
			];
			Do[
                {new, usedDefs, cond} = replaceAllAndTrack[ formula@k[[j]], filterRules[ rules, None]];
                If[ usedDefs =!= {} && freeVariables[ cond] === {},
                    (* rewrite applied *)
                    newForm = makeAssumptionFML[ formula -> new];
					If[ !TrueQ[ cond],
						AppendTo[ defCond, cond];
						AppendTo[ usedInCond, k[[j]]]
					];
                    appendToKB[ newK, newForm];
                    AppendTo[ genForms, {newForm}];
                    With[ {defs = Union[ usedDefs]},
                    	AppendTo[ usedForms, Prepend[ defs, k[[j]]]];
						AppendTo[ replBy, defs]
                    ];
                    defExpand = True,
                    (* else: no def expansion in this formula *)
                    Block[ {$autoGenerateRules = False}, appendToKB[ newK, k[[j]]]] (* rewrite rules from this formula are already there *)
                ],
                {j, Length[ k]}
            ];
            If[ defExpand,
            	newGoals = {toBeProved[ goal -> newG, kb -> newK, "AuxiliaryKB" -> Join[ auxKB, Flatten[ usedForms]], rest]};
            	If[ defCond =!= {},
            		(* conditions generated *)
            		(* To be done: When we are in a proof by contradiction we have to take care. Verifying conditions should not be done on the basis of a contradictiong KB.
            		   At the moment: no contradiction proof and the only termination rule active is goalInKB, maybe this is good enough. *)
            		newForm = makeGoalFML[ formula -> makeConjunction[ defCond, And$TM]];
            		AppendTo[ newGoals, 
            			Apply[ toBeProved[ goal -> newForm, kb -> newK, "AuxiliaryKB" -> Join[ auxKB, Flatten[ usedForms]], ##]&, 
            				setRuleActivity[ {contradiction -> False, contradictionKB -> False, contradictionUniv1 -> False, contradictionUniv2 -> False, falseInKB -> False}, rest]]];
            		AppendTo[ usedForms, usedInCond];
            		AppendTo[ genForms, {newForm}];
            		(* otherwise do nothing *)
            	];
            	(*
            		If no conditions have been generated, then newGoals contains only ONE SUBGOAL, otherwise we have TWO SUBGOALS.
            		In the latter case, the last element of usedForms is non-empty and the last element in genForms is a singleton list containing the condition. 
            		We pass an optional "defCond" -> True/False such that the proof text can be generated accordingly.
            	*)
            	(* We have to explicitly specify generated-> because we need the proper nesting *)
            	makeANDNODE[ makePRFINFO[ name -> expandDef, used -> usedForms, generated -> genForms, "defCond" -> (defCond =!= {}), "usedDefs" -> replBy], 
					newGoals],
				$Failed
            ]
		]
	]
]

setRuleActivity[ l_List, o1___, ruleActivity -> a_, o2___] := 
	Module[ {new},
		new = a /. Map[ ReplacePart[ #, 2 -> _] -> #&, l];
		{o1, ruleActivity -> new, o2}
	]
setRuleActivity[ args___] := unexpected[ setRuleActivity, {args}]


(* ::Section:: *)
(* Implicit Definitions *)

inferenceRule[ implicitDef] = 
ps:PRFSIT$[ g_, K_List, id_, rest___?OptionQ] :> performProofStep[
	Module[ {implDefPos, implDefTerms, k, checkRule, delPos = {}, subst = {}, newK, usedPos, newG, usedCond, allUsed, allGenerated, substKB = K, newForm}, 
		implDefPos = Position[ K, _?(!FreeQ[ #, EqualDef$TM[ _, (_Such$TM|_SuchUnique$TM)]]&), {1}];
		Do[
			{implDefTerms, checkRule} = getDefInstances[ {g, K}, formula@Extract[ K, implDefPos[[k]]]];
			If[ implDefTerms =!= $Failed,
				If[ implDefTerms === {},
					(* there are no terms to which this definition could apply, we mark the defintion to be removed from the KB *)
					AppendTo[ delPos, implDefPos[[k]]],
					(* else *)
					{subst, newK} = makeImplDefSubst[ implDefTerms, checkRule, Map[ formula, K]];
					Which[
						Length[ subst] === 0,
						(* no subst possible, try next def *)
						Continue[],
						Length[ subst] === Length[ implDefTerms],
						(* all possible terms will be substituted, we can remove the definition.*)
						AppendTo[ delPos, implDefPos[[k]]]
						(* otherwise nothing needs to be done, we exit the loop with the Break, but we keep the defintion for possible later substitution *)
					];
					usedPos = implDefPos[[k]];
					Break[]
				]
			],
			{k, Length[ implDefPos]}
		];
		If[ Length[ subst] === 0,
			If[ delPos === {},
				(* new def applicable, no def removable *)
				$Failed,
				(* some defs can be removed from the KB *)
				makeANDNODE[ makePRFINFO[ name -> implicitDef, used -> {}], 
            		toBeProved[ goal -> g, kb -> Delete[ K, delPos], rest]
				]
			],
			(* else: do the substitutions *)
			{newG, usedCond} = Reap[ formula@g /. subst];
			If[ usedCond === {},
				(* no subst in goal *)
				newG = g;
				allUsed = {{}};
				allGenerated = {{}},
				(* new goal by substitution *)
				(* Reap gives a list with only one list (all Sows without tag) of positions. We take this one list and form the union of positions *)
				allUsed = {Join[ {g, Extract[ K, usedPos]}, Extract[ K, Apply[ Union, usedCond[[1]]]]]};
				newG = makeGoalFML[ formula -> newG];
				allGenerated = {{newG}}
			];
			(* Do the same like for goal for all in KB *)
			Do[
				If[ {k} === usedPos, Continue[]]; (* don't rewrite the def itself *)
				{newForm, usedCond} = Reap[ formula@K[[k]] /. subst];
				If[ usedCond === {},
					Continue[],
					AppendTo[ allUsed, Join[ {K[[k]], Extract[ K, usedPos]}, Extract[ K, Apply[ Union, usedCond[[1]]]]]];
					newForm = makeAssumptionFML[ formula -> newForm];
					AppendTo[ allGenerated, {newForm}];
					(* we don't generate rewrite rules for the subst form, because it will not become a rewrite formula if it wasn't one before *)
					substKB = ReplacePart[ substKB, k -> newForm];
				],
				{k, Length[ K]}
			];
			(* Eventually delete superfluous defs. Don't do this earlier, because otherwise positions of used assumptions might get mixed up *)
			substKB = Delete[ substKB, delPos];
			(* add the characteristic properties to the KB and register them as newly generated *)
			PrependTo[ allUsed, {Extract[ K, usedPos]}];
			PrependTo[ allGenerated, Map[ makeAssumptionFML[ formula -> #]&, newK]];
        	makeANDNODE[ makePRFINFO[ name -> implicitDef, used -> allUsed, generated -> allGenerated,
        								"introConstFor" -> Map[ Extract[ #, {{2, 2}, {1}}]&, subst]], 
            	toBeProved[ goal -> newG, kb -> joinKB[ allGenerated[[1]], substKB], rest]
        	]
		]
	]
]

makeImplDefSubst[ terms_List, def_RuleDelayed, K_List] :=
	Module[ {k, newBody, abf, fix, allSubst = {}, newK = {}},
		Do[
			newBody = Replace[ {terms[[k]], K}, def];
			If[ newBody === {},
				(* condition of the implicit definition is not fulfilled for this term *)
				Continue[],
				(* else *)
				{abf, fix} = arbitraryButFixed[ newBody[[2]], newBody[[1]], {K, newK}];
				(* newBody can only have the ONE variable from the such-quantifier as free variable, hence there is only ONE constant in fix *)
				AppendTo[ allSubst, With[ {pos = newBody[[3]], const = rngConstants[ fix][[1]]}, terms[[k]] :> (Sow[ pos]; const)]];
				AppendTo[ newK, abf];
			],
			{k, Length[ terms]}
		];
		{allSubst, newK}
	]
makeImplDefSubst[ args___] := unexpected[ makeImplDefSubst, {args}]

(* ::Section:: *)
(* Instantiation *)

(*
  We assume the local info of the PRFSIT has an entry "constants" -> L. The list L is a list of elementary ranges, e.g. SIMPRNG$, SETRNG$, etc.
  Elements of the form RNG$[...] in L are ranges that have not yet been processed for instantiation, i.e. if L is free of RNG$_ then there
  are no new contants for instantiation, otherwise we need to instantiate using RNG$ and then add the ranges (without the RNG$ wrapper) to L.
*)

inferenceRule[ instantiate] = 
ps:PRFSIT$[ g_, K_List, id_, rest___?OptionQ] :> performProofStep[
	Module[ {oldConst, newConst, univKB, instForm, orig = {}, new = {}, inst = {}, i}, 
		{newConst, oldConst} = constants[ ps];
		If[ newConst === {},
			Throw[ $Failed]
		];
		univKB = Cases[ K, FML$[ _, _Forall$TM, _]];       
        instForm = Replace[ univKB, FML$[ k_, f_, r___] :> instantiateForall[ FML$[ k, standardFormQuantifier[ f], r], newConst], {1}];
        (* for each form in univKB we get a list {forms, inst}, where
            forms is a list of instantiations of form and
            inst is a list of substitutions, such that inst_i applied to form gives forms_i.
        *)
        Do[
            If[ instForm[[ i, 1]] === {},
                Continue[],
                (* else *)
                AppendTo[ orig, {univKB[[i]]}];
                AppendTo[ new, instForm[[ i, 1]]];
                AppendTo[ inst, instForm[[ i, 2]]]
            ],
            {i, Length[ instForm]}
        ];
        (* We have to explicitly specify generated-> because we need the proper nesting *)
        makeANDNODE[ makePRFINFO[ name -> instantiate, used -> orig, generated -> new, "instantiation" -> inst], 
            toBeProved[ goal -> g, kb -> Fold[ joinKB[ #2, #1]&, K, new], "constants" -> Join[ Apply[ List, newConst], oldConst], rest]
        ]
	]
]

constants[ ps_PRFSIT$] :=
	Module[{L = getOptionalComponent[ ps, "constants"], new, old},
		new = Cases[ L, _RNG$];
		old = Complement[ L, new];
		{Apply[ Join, new], old}
	]
constants[ args___] := unexpected[ constants, {args}]

getAllConstants[ ps_PRFSIT$] :=
   (* constants in local info can be a mixture of elementary ranges (e.g. SETRNG$) and
	ranges wrapped in RNG$ (constants that have not yet been used for instantiation).
	We just eliminate the RNG$'es to get a flat list of elementary ranges *)
    getOptionalComponent[ ps, "constants"] /. RNG$ -> Sequence;
getAllConstants[ args___] := unexpected[ getAllConstants, {args}]


instantiateForall[ f:FML$[ _, Forall$TM[ R1_RNG$, C_, A_], __], R2_RNG$] :=
    Module[ {possibleInst = Select[ Tuples[ {R1, R2}], compatibleRange], groupVar, inst = {}, subst = {}, S, i},
    	(* we run over the possible pairs and sow them with their first element (the variable to be instantiated) as tag, i.e.
    	   pairs are grouped into different lists with identical var within each list. *)
    	If[ possibleInst =!= {},
    		groupVar = Reap[ Scan[ Sow[ #, First[ #]]&, possibleInst]];
    		(* now we take all tuples, which then gives all possible combinations of instantiations. 
    	   	   has the advantage that we *)
    		possibleInst = Tuples[ groupVar[[2]]]
    	];
        Do[
        	S = Map[ Rule[ #[[1, 1]], #[[2, 1]]]&, possibleInst[[i]]];
        	With[ {new = substituteFree[ simplifiedForall[ Forall$TM[ DeleteCases[ R1, Apply[ Alternatives, Map[ First, possibleInst[[i]]]]], C, A]], S]},
        		If[ new =!= $Failed,
        			AppendTo[ inst, makeAssumptionFML[ formula -> new]];
        			AppendTo[ subst, S]
        		]
        	],
        	{i, Length[ possibleInst]}
        ];
        {inst, subst}
    ]
instantiateForall[ args___] := unexpected[ instantiateForall, {args}]

compatibleRange[ {SIMPRNG$[ _], _}] := True
compatibleRange[ {STEPRNG$[ _, l1_Integer, u1_Integer, s_], STEPRNG$[ _, l2_Integer, u2_Integer, s_]}] /; l1 <= l2 && u1 >= u2 := True
compatibleRange[ {SETRNG$[ _, s_], SETRNG$[ _, s_]}] := True
compatibleRange[ {PREDRNG$[ _, s_], PREDRNG$[ _, s_]}] := True
compatibleRange[ {_, _}] := False
compatibleRange[ args___] := unexpected[ compatibleRange, {args}]


(* ::Section:: *)
(* unification *)

(* in both cases: check used and generated more thoroughly, whether they are correctly passed *)

inferenceRule[ solveMetaUnification] = 
ps:(PRFSIT$[ g:FML$[ _, a_And$TM, lab_, ___] /; MemberQ[ a, e_Equal$TM /; !FreeQ[ e, _META$]], K_List, id_, rest___?OptionQ]|
PRFSIT$[ g:FML$[ _, e_Equal$TM /; !FreeQ[ e, _META$], lab_, ___], K_List, id_, rest___?OptionQ]) :> performProofStep[
	Module[ {eq, com, inst, newGoalsAlt},
		If[ Head[ formula@g] === Equal$TM,
		  eq = {e},
		  (* else *)
		  eq = Cases[ a, s_Equal$TM /; !FreeQ[ s, _META$], {1}, 1]
		];
		{com, inst} = Apply[ unification, eq[[1]]];
		If[ com === $Failed,
			Throw[ $Failed]
		];
		newGoalsAlt = DeleteCases[ Map[ instantiateMeta[ formula@g, #]&, inst], $Failed];	(* 'inst' is a list of instantiations! *)
		newGoalsAlt = DeleteCases[ Map[ Catch[ makeGoalFML[ formula -> #]]&, newGoalsAlt], $Failed];	(* remove all ill-formed goals *)
		Switch[ newGoalsAlt,
			{},
			$Failed,
			
			{_},
			makeANDNODE[ makePRFINFO[ name -> solveMetaUnification, used -> g, "instantiation" -> inst], 
            	toBeProved[ goal -> newGoalsAlt[[1]], kb -> K, rest]
        	],
        	
			_,
        	makeORNODE[ makePRFINFO[ name -> solveMetaUnification, used -> g, "instantiation" -> inst], 
            	Map[ toBeProved[ goal -> #, kb -> K, rest]&, newGoalsAlt]
        	]
		]
	]
]

simplifiedProofInfo[ pi_, n_Integer] /; name@pi === solveMetaUnification := 
	Module[ {p = Position[ pi, "instantiation" -> _]},
		MapAt[ #[[n]]&, pi, Join[ {{2}, {3}}, p]]
	]
	
inferenceRule[ partSolveMetaMatching] = 
ps:(PRFSIT$[ g:FML$[ _, a:And$TM[ pre___, x_ /; !FreeQ[ x, _META$], post___], lab_, ___], K_List, id_, rest___?OptionQ]|
PRFSIT$[ g:FML$[ _, a:x_ /; !FreeQ[ x, _META$], lab_, ___], K_List, id_, rest___?OptionQ]) :> performProofStep[
	Module[ {inst = Map[ instantiation[ x, formula@#]&, K], posInst, newGoalsAlt},
		posInst = Position[ inst, _List, {1}];
		If[ posInst === {},
			Throw[ $Failed],
			(* else *)
			inst = Extract[ inst, posInst];
		];
		newGoalsAlt = DeleteCases[ Map[ instantiateMeta[ a, #]&, inst], $Failed];	(* 'inst' is a list of instantiations! *)
		newGoalsAlt = DeleteCases[ Map[ Catch[ makeGoalFML[ formula -> #]]&, newGoalsAlt], $Failed];	(* remove all ill-formed goals *)
		Switch[ newGoalsAlt,
			{},
			$Failed,
			
			{_},
			makeANDNODE[ makePRFINFO[ name -> partSolveMetaMatching, used -> g, "instantiation" -> inst], 
            	toBeProved[ goal -> newGoalsAlt[[1]], kb -> K, rest]
        	],
        	
			_,
        	makeORNODE[ makePRFINFO[ name -> partSolveMetaMultiMatching, used -> g, "instantiation" -> inst], 
            	Map[ toBeProved[ goal -> #, kb -> K, rest]&, newGoalsAlt]
        	]
		]
	]
]

simplifiedProofInfo[ pi_, n_Integer] /; name@pi === partSolveMetaMatching := 
	Module[ {p = Position[ pi, "instantiation" -> _]},
		MapAt[ {#[[n]]}&, MapAt[ #[[n]]&, pi, {{2}, {3}}], Insert[ p, 2, {1, 2}]]
	]
	

inferenceRule[ maxTuples1] = 
ps:PRFSIT$[ g:FML$[ _, GreaterEqual$TM[ Subtract$TM[ 
	m1:max$TM[ t1:ReplacePart$TM[ s_, Tuple$TM[ i_, a_]]], 
    m2:max$TM[ t2:DeleteAt$TM[ s_, i_]]], 0], lab_, ___], K_List, id_, rest___?OptionQ] :> performProofStep[
	Module[ {},
		makeTERMINALNODE[ makePRFINFO[ name -> maxTuples1, used -> g, "comp" -> {t1, t2, a, GreaterEqual$TM[ m1, m2]}], proved]
	]
]

inferenceRule[ inequality1] = 
ps:PRFSIT$[ g:FML$[ _, GreaterEqual$TM[ 0, Subtract$TM[ x_, y_]], ___], 
	{___, k:FML$[ _, LessEqual$TM[ x_, y_], ___], ___}, id_, rest___?OptionQ] :> performProofStep[
	Module[ {},
		makeTERMINALNODE[ makePRFINFO[ name -> inequality1, used -> {g, k}], proved]
	]
]

inferenceRule[ memberCases] = 
ps:PRFSIT$[ g_, 
	{pre___, k1:FML$[ _, Theorema`Language`Element$TM[ x_, A_], ___], mid___, k2:FML$[ _, Theorema`Language`Element$TM[ y_, A_], ___], post___}, id_, rest___?OptionQ] :> performProofStep[
	Module[ {case1, case2},
		case1 = makeAssumptionFML[ formula -> Equal$TM[ x, y]];
		case2 = makeAssumptionFML[ formula -> Unequal$TM[ x, y]];
		makeANDNODE[ makePRFINFO[ name -> memberCases, used -> {{k1, k2}, {k1, k2}}], 
			{Block[ {$rewriteRules = {}}, toBeProved[ goal -> g, kb -> prependKB[{pre, mid, post}, case1], rest]],
			 Block[ {$rewriteRules = {}}, toBeProved[ goal -> g, kb -> prependKB[{pre, mid, post, k2}, case2], rest]]}
		]
	]
]



(* ::Section:: *)
(* Rule composition *)

terminationRules = {"Termination Rules",
	{goalInKB, True, True, 1, "term"},
	{falseInKB, True, True, 1, "term"},
	{trueGoal, True, True, 1, "term"},
	{contradictionKB, True, True, 1, "term"},
	{contradictionUniv1, True, True, 2, "term"},
	{contradictionUniv2, True, True, 2, "term"}
	};

connectiveRules = {"Connectives Rules", 
	{notGoal, True, True, 30},
	{deMorganKB, True, True, 5},
	{andGoal, True, True, 6},
	{andKB, True, False, 5},
	{orGoal, True, True, 5},
	{orKB, True, True, 19},
	{implGoalDirect, True, True, 5},
	{implGoalCP, False, False, 10},
	{implKBCases, True, True, 22},
	{equivGoal, True, True, 10}};

equalityRules = {"Equality Rules", 
	{eqGoal, False, False, 20}
	};
	
rewritingRules = {"Rewriting Rules",
	{goalRewriting, True, True, 22},
	{knowledgeRewriting, True, True, 25},
	{elementarySubstitution, True, True, 8},
	{expandDef, True, True, 80},
	{implicitDef, True, True, 80}
};

registerRuleSet[ "Quantifier Rules", quantifierRules, {
	{forallGoal, True, True, 10},
	{forallKB, True, True, 40, "levelSat1"},
	{forallKBInteractive, False, True, 42},
	{instantiate, True, True, 35},
	{existsGoal, True, True, 10},
	{existsGoalInteractive, False, True, 12},
	{existsKB, True, True, 11},
	{partSolveMetaMatching, True, True, 8},
	{solveMetaUnification, True, True, 9}
	}]

registerRuleSet[ "Special Arithmetic", specialArithmeticRules, {
	{inequality1, True, True, 2, "term"},
	{maxTuples1, True, True, 2, "term"},
	{memberCases, True, True, 30}
	}]

registerRuleSet[ "Basic Theorema Language Rules", basicTheoremaLanguageRules, {
	terminationRules,
	quantifierRules, 
	connectiveRules, 
	equalityRules,
	rewritingRules,
	specialArithmeticRules,
	{contradiction, False, True, 100}
	}]

End[]

EndPackage[]