(* Theorema 
    Copyright (C) 2010 The Theorema Group

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
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
Modus Ponens is superseded by the much more general rewriting technique
*)

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
ps:PRFSIT$[ g:FML$[ _, u:Forall$TM[ rng_, cond_, A_], __], k_List, id_, rest___?OptionQ] :> performProofStep[
	Module[ {faBui, simp, rc, r, c, f, fix, newConds, newGoal, locC},
		(* we use computation regardless whether it is activated or not ... *)
		faBui = buiActProve[ "Forall"];
		buiActProve[ "Forall"] = True;
		simp = computeInProof[ u];
		buiActProve[ "Forall"] = faBui;
		If[ MatchQ[ simp, _Forall$TM],
			(* no simplification *)
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
			],
			(* else *)
			simp = makeGoalFML[ formula -> simp];
			makeANDNODE[ makePRFINFO[ name -> forallGoal, used -> g], 
				toBeProved[ goal -> simp, kb -> k, rest]]
		]
	]
]

inferenceRule[ forallKB] = 
ps:PRFSIT$[ g_, K:{___, f:FML$[ _, _Forall$TM, __], ___}, id_, rest___?OptionQ] :> performProofStep[
	Module[ {faInst, fk = key@f, newConst, oldConst, inst},
	    faInst = getOptionalComponent[ ps, "forallKB"];
	    If[ MemberQ[ faInst, fk],
                (* Rule forallKB has already been applied for those forms *)
	        Throw[ $Failed]
	    ];
	    {newConst, oldConst} = constants[ ps];
        (* we instantiate with the "old" constants only, because the new ones will be treated by the 'instantiate'-rule separately *)
	    inst = instantiateForall[ f, Apply[ RNG$, oldConst]];
	    makeANDNODE[ makePRFINFO[ name -> forallKB, used -> f, "instantiation" -> inst[[2]]], 
	        toBeProved[ goal -> g, kb -> joinKB[ inst[[1]], K], "forallKB" -> Prepend[ faInst, fk], rest]]
	]
]

inferenceRule[ forallKBInteractive] = 
ps:PRFSIT$[ g_, K:{___, f:FML$[ _, Forall$TM[ rng_, cond_, A_], __], ___}, id_, rest___?OptionQ] :> performProofStep[
    Module[ {rc, r, c, Ainst, fInst, inst},
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
            	newGoal = makeGoalFML[ formula -> makeExist[ thinnedRng, rc, cond, A, subst]];
            	makeANDNODE[ makePRFINFO[ name -> existsGoalInteractive, used -> g, "instantiation" -> subst], 
                	toBeProved[ goal -> newGoal, kb -> k, rest]]
            ]
        ]
    ]
]

makeExist[ RNG$[], cond1_List, cond2_, A_, subst_] := Apply[ And$TM, substituteFree[ DeleteCases[ Join[ cond1, {cond2, A}], True], subst]]
makeExist[ r:RNG$[__], cond1_List, cond2_, A_, subst_] := 
	Exists$TM[ r, True, Apply[ And$TM, substituteFree[ DeleteCases[ Join[ cond1, {cond2, A}], True], subst]]]
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
this:PRFSIT$[ g:FML$[ _, _?isAtomicExpression, __], k_List, id_, rest___?OptionQ] :> performProofStep[
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
(* substitution *)

inferenceRule[ elementarySubstitution] = 
ps:PRFSIT$[ g_, k_List, id_, rest___?OptionQ] :> performProofStep[
	Module[ {rules, usedSubst, cond, newForm, newG, substCond = {}, usedInCond = {}, newK = {}, substApplied = False, j, usedForms, genForms, replBy = {}},
		rules = substRules@ps;
		If[ rules === {},
			(* There are no substitutions available -> rule does not apply *)
			$Failed,
			(* else: we have substitutions *)
			{newForm, usedSubst, cond} = replaceRepeatedAndTrack[ formula@g, rules];
			If[ usedSubst =!= {},
				(* rewrite applied *)
				newG = makeGoalFML[ formula -> newForm];
				If[ !TrueQ[ cond],
					AppendTo[ substCond, cond];
					AppendTo[ usedInCond, g]
				];
				substApplied = True,
				(* else: no subst in goal *)
				newG = g
			];
			(* The first used and generated are old/new goal. If they are identical, then the proof header won't print any text for the goal part *)
			usedForms = {{g}};
			genForms = {{newG}};
			AppendTo[ replBy, Union[ usedSubst]];
			Do[
                {newForm, usedSubst, cond} = replaceRepeatedAndTrack[ formula@k[[j]], rules];
                If[ usedSubst =!= {},
                    (* rewrite applied *)
                    newForm = makeAssumptionFML[ formula -> newForm];
                    If[ !TrueQ[ cond],
						AppendTo[ substCond, cond];
						AppendTo[ usedInCond, k[[j]]]
					];
                    appendToKB[ newK, newForm];
                    AppendTo[ usedForms, {k[[j]]}];
                    AppendTo[ genForms, {newForm}];
					AppendTo[ replBy, Union[ usedSubst]];
                    substApplied = True,
                    (* else: no subst in this formula *)
                    Block[ {$autoGenerateRules = False}, appendToKB[ newK, k[[j]]]] (* rewrite rules from this formula are already there *)
                ],
                {j, Length[ k]}
            ];
            (* Proof goals for checking the conditions are still missing *)
            If[ substApplied,
            	(* We have to explicitly specify generated-> because we need the proper nesting *)
            	makeANDNODE[ makePRFINFO[ name -> elementarySubstitution, used -> usedForms, generated -> genForms, "usedSubst" -> replBy], 
					toBeProved[ goal -> newG, kb -> newK, rest]],
				$Failed
            ]
		]
	]
]

(* ::Section:: *)
(* Expand Definitions *)

inferenceRule[ expandDef] = 
ps:PRFSIT$[ g_, k_List, id_, rest___?OptionQ] :> performProofStep[
	Module[ {rules, usedDefs, cond, new, newG, newForm, newK = {}, defExpand = False, defCond = {}, usedInCond = {}, j, usedForms, genForms, replBy = {}, newGoals},
		rules = defRules@ps;
		If[ rules === {},
			(* There are no definitions available at all in this proof -> expanding defs does not apply *)
			$Failed,
			(* else: we have definition rewrite rules *)
			{new, usedDefs, cond} = replaceAllAndTrack[ formula@g, rules];
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
			usedForms = {{g}};
			genForms = {{newG}};
			AppendTo[ replBy, Union[ usedDefs]];
			Do[
                {new, usedDefs, cond} = replaceAllAndTrack[ formula@k[[j]], rules];
                If[ usedDefs =!= {} && freeVariables[ cond] === {},
                    (* rewrite applied *)
                    newForm = makeAssumptionFML[ formula -> new];
					If[ !TrueQ[ cond],
						AppendTo[ defCond, cond];
						AppendTo[ usedInCond, k[[j]]]
					];
                    appendToKB[ newK, newForm];
                    AppendTo[ usedForms, {k[[j]]}];
                    AppendTo[ genForms, {newForm}];
					AppendTo[ replBy, Union[ usedDefs]];
                    defExpand = True,
                    (* else: no def expansion in this formula *)
                    Block[ {$autoGenerateRules = False}, appendToKB[ newK, k[[j]]]] (* rewrite rules from this formula are already there *)
                ],
                {j, Length[ k]}
            ];
            If[ defExpand,
            	newGoals = {toBeProved[ goal -> newG, kb -> newK, rest]};
            	If[ defCond =!= {},
            		newForm = makeGoalFML[ formula -> makeConjunction[ defCond, And$TM]];
            		AppendTo[ newGoals, toBeProved[ goal -> newForm, kb -> k, rest]],
            		(* else *)
            		newForm = True
            	];
            	(*
            		If no conditions have been generated, then newGoals contains only ONE SUBGOAL and the last element of usedForms is {}.
            		Otherwise, we have TWO SUBGOALS, and the last element of usedForms is non-empty. We can rely on this when generating the proof text.
            	*)
            	AppendTo[ usedForms, usedInCond];
            	AppendTo[ genForms, {newForm}];
            	(* We have to explicitly specify generated-> because we need the proper nesting *)
            	makeANDNODE[ makePRFINFO[ name -> expandDef, used -> usedForms, generated -> genForms, "usedDefs" -> replBy], 
					newGoals],
				$Failed
            ]
		]
	]
]

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
        instForm = Map[ instantiateForall[ #, newConst]&, univKB];
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
    Module[ {possibleInst = Select[ Tuples[ {R1, R2}], compatibleRange], inst = {}, subst = {}, S, i},
        Do[
        	S = MapThread[ Rule, {rngVariables[ RNG$[ possibleInst[[i, 1]]]], rngConstants[ RNG$[ possibleInst[[i, 2]]]]}];
            AppendTo[ inst, makeAssumptionFML[ formula -> substituteFree[ simplifiedForall[ Forall$TM[ DeleteCases[ R1, possibleInst[[i, 1]]], C, A]], S]]];
            subst = Join[ subst, S],
        	{i, Length[ possibleInst]}
        ];
        {inst, subst}
    ]
instantiateForall[ args___] := unexpected[ instantiateForall, {args}]

compatibleRange[ {SIMPRNG$[ _], _}] := True
compatibleRange[ {STEPRNG$[ _, l1_Integer, u1_Integer, s_], STEPRNG$[ _, l2_Integer, u2_Integer, s_]}] /; l1 <= l2 && u1 >= u2 := True
compatibleRange[ {SETRNG$[ _, s_Set$TM], SETRNG$[ _, s_Set$TM]}] := True
compatibleRange[ {_, _}] := False
compatibleRange[ args___] := unexpected[ compatibleRange, {args}]


(* ::Section:: *)
(* Rule composition *)

terminationRules = {"Termination Rules",
	{goalInKB, True, True, 1, "term"},
	{falseInKB, True, True, 1, "term"},
	{trueGoal, True, True, 1, "term"},
	{contradictionKB, True, True, 1, "term"}
	};

connectiveRules = {"Connectives Rules", 
	{notGoal, True, True, 30},
	{andGoal, True, True, 5},
	{andKB, True, False, 5},
	{orGoal, True, True, 5},
	{orKB, True, True, 19},
	{implGoalDirect, True, True, 5},
	{implGoalCP, False, False, 10},
	{modusPonens, True, True, 30, "levelSat2"},
	{equivGoal, True, True, 10}};

equalityRules = {"Equality Rules", 
	{eqGoal, False, False, 20}
	};

registerRuleSet[ "Quantifier Rules", quantifierRules, {
	{forallGoal, True, True, 10},
	{forallKB, True, True, 40, "levelSat1"},
	{forallKBInteractive, False, True, 42},
	{instantiate, True, True, 35},
	{existsGoal, True, True, 10},
	{existsGoalInteractive, False, True, 12},
	{existsKB, True, True, 11}
	}]

registerRuleSet[ "Basic Theorema Language Rules", basicTheoremaLanguageRules, {
	terminationRules,
	quantifierRules, 
	connectiveRules, 
	equalityRules,
	{goalRewriting, True, True, 15},
	{knowledgeRewriting, True, True, 25},
	{elementarySubstitution, True, True, 4},
	{expandDef, True, True, 80},
	{contradiction, True, True, 100}
	}]

End[]

EndPackage[]