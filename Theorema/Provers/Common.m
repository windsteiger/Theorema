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

BeginPackage["Theorema`Provers`Common`"]

Needs[ "Theorema`Common`"]
Needs[ "Theorema`Language`"]
Needs[ "Theorema`Provers`"]

Begin["`Private`"]


(* ::Section:: *)
(* Prover call *)

(* ::Subsubsection:: *)
(* callProver *)

initProver[] :=
	Module[ {},
		$TMAproofTree = {};
		$registeredRuleSets = {};
		$registeredStrategies = {};
		Clear[ ruleTextActive];
		ruleTextActive[_] := True;
		$proofCellStatus = Automatic;
		$TMAcurrentDepth = 1;
		$TMAproofSearchRunning = False;
		$rewriteRules = {};
		$generated = {};
		$autoGenerateRules = True;
	]

callProver[ ruleSetup:{_Hold, _List, _List}, strategy_, goal_FML$, kb_List, searchDepth_Integer, searchTime:(_Integer|Infinity)] :=
	Module[ {timeElapsed},
		$rewriteRules = {};
		$generated = {};
		$TMAproofSearchRunning = True;
		$TMAcurrentDepth = 2;
		$TMAproofTree = makeInitialProofTree[ ];
		$TMAproofObject = makeInitialProofObject[ goal, kb, ruleSetup, strategy];
		$TMAcheckSuccess = True;
		Clear[ $TMAproofNotebook];
		initFormulaLabel[];
		$lastChoice = {};
		timeElapsed = proofSearch[ searchDepth, searchTime];
		$TMAproofSearchRunning = False;
		{proofValue@$TMAproofObject, $TMAproofObject, $TMAproofTree, timeElapsed}
	]
callProver[ args___] := unexpected[ callProver, {args}]


(* ::Subsubsection:: *)
(* proofSearch *)

proofSearch[ searchDepth_Integer, searchTime:(_Integer|Infinity)] :=
    Module[ {startTime = SessionTime[], openPSpos, selPSpos, selPS, pStrat, newSteps},
    	$proofAborted = False;
        (* As long as there is something to do, run the basic search loop.
           Time limit not reached, proof not aborted interactively, proof still pending, open proof sits available.
           If pending, then open proof sits should be available, still we check to be on the save side, otherwise
           choosing the next sit might lead to errors. We need to extract the open sits anyway, so the effort is not in vain.
        *)
        While[ SessionTime[] - startTime <= searchTime && !$proofAborted && proofValue@$TMAproofObject === pending && 
        	(openPSpos = positionRelevantSits[ $TMAproofObject]) =!= {},
        	(* choose the next proof sit to continue *)
            {selPS, selPSpos} = chooseNextPS[ openPSpos];
            $currentSearchLevel = Length[ selPSpos];
            (* we record the depth of the tree, it is a parameter for computing the size for displaying the proof tree in the GUI *)
            $TMAcurrentDepth = Max[ $TMAcurrentDepth, $currentSearchLevel];
            If[ $currentSearchLevel > searchDepth,
            (* if search depth limit is reached, put a failing leaf *)
            	newSteps = searchDepthExceeded[ selPS],
            	(* else: if search depth limit is not yet reached ...*)
            	(* get the strategy from the proof sit ...*)
            	pStrat = strategy@selPS;
            	(* and apply it to the selected proof sit*)
            	newSteps = pStrat[ selPS]
            ];
            (* Security check: if newSteps is something invalid (should never be, but buggy strategy or buggy rules could do that *)
            If[ !isProofNode[ newSteps],
            	newSteps = noProofNode[ newSteps, id@selPS];
			];
			(* replace the open proof sit with the new subtree ...*)
            $TMAproofObject = replaceProofSit[ $TMAproofObject, selPSpos -> newSteps];
            (* and propagate the proof value *)
            $TMAproofObject = propagateProofValues[ $TMAproofObject];
        ];
        (* return value: elapsed time *)
        SessionTime[] - startTime
    ]
proofSearch[ args___] := unexpected[ proofSearch, {args}]


(* ::Subsubsection:: *)
(* Experimental feature: prallel proof search *)

(* This needs more thoughts, how to update the proof tree when parallel modifications may take place.
   Just as a starting point ... *)
proofSearchParallel[ searchDepth_Integer] :=
    Module[ {openPSpos},
    	$proofAborted = False;
    	SetSharedVariable[$TMAproofObject, $TMAproofTree];
        While[ !$proofAborted && proofValue@$TMAproofObject === pending && (openPSpos = positionRelevantSits[ $TMAproofObject]) =!= {},
        	ParallelTry[ proofSearchAtPos[ #, searchDepth]&, openPSpos];
        ]
    ]
proofSearchParallel[ args___] := unexpected[ proofSearchParallel, {args}]

Clear[ proofSearchAtPos];
proofSearchAtPos[ selPSpos_List, searchDepth_Integer] :=
    Module[ {selPS, pStrat, newSteps},
        selPS = Extract[ $TMAproofObject, selPSpos];
        If[ Length[ selPSpos] > searchDepth,
            newSteps = searchDepthExceeded[ selPS],
            (* else *)
            pStrat = strategy@selPS;
            newSteps = pStrat[ selPS]
        ];
        If[ !isProofNode[ newSteps],
            newSteps = noProofNode[ newSteps, id@selPS];
        ];
        $TMAproofObject = replaceProofSit[ $TMAproofObject, selPSpos -> newSteps];
        $TMAproofObject = propagateProofValues[ $TMAproofObject]
    ]
proofSearchAtPos[ args___] := unexpected[ proofSearchAtPos, {args}]

(*
	An open proof situation under a failing ANDNODE$ or a proved ORNODE$ is not relevant (in the remaining proof search).
	positionRelevantSits[ po] searches all open positions and then selects only the relevant ones.
	We can assume, that the proof value of po is pending, otherwise we would not call this function.
*)
positionRelevantSits[ po_PRFOBJ$] :=
	Module[{allPending},
		allPending = Position[ po, _PRFSIT$];
		Select[ allPending, stillRelevant[ #, po]&]
	]
positionRelevantSits[ args___] := unexpected[ positionRelevantSits, {args}]

stillRelevant[ pos_List, po_PRFOBJ$] :=
	Module[{path = Drop[ pos, -1], node},
		(* Given the node at position pos, we follow the path upwards and check all parent nodes *)
		While[ path =!= {},
			node = Extract[ po, path];
			If[ (type@node === ANDNODE$ && proofValue@node === failed) ||
				(type@node === ORNODE$ && proofValue@node === proved),
				Return[ False]
			];
			path = Drop[ path, -1];
		];
		True
	]
stillRelevant[ args___] := unexpected[ stillRelevant, {args}]

chooseNextPS[ allPending:{pendingPos_, ___}] /; $interactiveProofSitSel && MatchQ[ $lastChoice, {___Integer}] && Length[ allPending] > 1 :=
	Module[ {node, pos = $lastChoice},
		Switch[ $lastChoice,
			{},
			findNextPendingSit[ $TMAproofObject, allPending, {}],
			
			_,
			node = Extract[ $TMAproofObject, $lastChoice];
			Switch[ node,
				_PRFSIT$,
				$selectedProofStep = id@node;
				{node, $lastChoice},
				
				_ANDNODE$|_ORNODE$|_TERMINALNODE$,
				Switch[ proofValue@node,
					pending,
					findNextPendingSit[ node, allPending, $lastChoice],
					_,
					pos = Most[ $lastChoice];
					node = Extract[ $TMAproofObject, pos];
					While[ proofValue@node =!= pending && pos =!= {},
						pos = Most[ pos];
						node = Extract[ $TMAproofObject, pos]
					];
					Switch[ proofValue@node,
						pending,
						$lastChoice = pos;
						findNextPendingSit[ node, allPending, $lastChoice],
						_,
						{Extract[ $TMAproofObject, pendingPos], pendingPos} (* Should not happen *)
					]
				],
				
				_,
				{Extract[ $TMAproofObject, pendingPos], pendingPos} (* Should not happen *)
			]
		]
	]
chooseNextPS[ psPos_List] /; $interactiveProofSitSel && !MatchQ[ $lastChoice, {___Integer}] :=
	(
		(* If $lastChoice not a list of integers, we assume it is the id of a node. *)
		$lastChoice = Position[ $TMAproofObject, (_PRFSIT$|_PRFOBJ$|_ANDNODE$|_ORNODE$|_TERMINALNODE$)?(id[ #] === $lastChoice &), {0, Infinity}, 1, Heads -> False];
		If[ $lastChoice =!= {}, $lastChoice = First[ $lastChoice]];
		chooseNextPS[ psPos]
	)
chooseNextPS[ psPos_List] :=
	Module[{openPS},
        openPS = Extract[ $TMAproofObject, psPos];
		Map[ First, {openPS, psPos}]
	]
(*
chooseNextPS[ psPos_List] /; $interactiveProofSitSel && Length[ psPos] > 1 :=
	Module[{ openPS, psSel},
		openPS = Extract[ $TMAproofObject, psPos];
		(*$selectedProofStep = id[ openPS[[1]]];*)
		nextProofSitDialog[ openPS];
		NotebookClose[ $TMAproofNotebook];
		{psSel} = Position[ openPS, _?(id[#] === $selectedProofStep&), {1}, Heads -> False];
		Map[ Extract[ #, psSel]&, {openPS, psPos}]
	]
*)
chooseNextPS[ args___] := unexpected[ chooseNextPS, {args}]

findNextPendingSit[ (PRFOBJ$|ANDNODE$)[ _PRFINFO$, b__, pending], psPos_List, pos_List] :=
	Module[ {p},
		(
			p = p[[1, 1]];
			findNextPendingSit[ Part[ {b}, p], psPos, Append[ pos, p + 1]]
		) /; (p = Position[ {b}, _?(proofValue[ #] === pending &), {1}, 1, Heads -> False]) =!= {}
	]
findNextPendingSit[ ORNODE$[ _PRFINFO$, b__, pending], psPos_List, pos_List] :=
	Module[ {p, openPS, psSel},
		Switch[ p,
			{_},
			(* If there is only one pending branch left, we do not ask the user. *)
			p = p[[1, 1]];
			findNextPendingSit[ Part[ {b}, p], psPos, Append[ pos, p + 1]],
			_,
			openPS = Extract[ $TMAproofObject, psPos];
			With[ {l = Length[ pos]},
				$selectedProofStep = id@Extract[ openPS, First[ Position[ psPos, _?(Length[ #] > l && Take[ #, l] === pos &), {1}, 1, Heads -> False]]]
			];
			nextProofSitDialog[ openPS];
			NotebookClose[ $TMAproofNotebook];
			{psSel} = Position[ openPS, _?(id[ #] === $selectedProofStep&), {1}, Heads -> False];
			$lastChoice = Extract[ psPos, psSel];
			{Extract[ openPS, psSel], $lastChoice}
		] /; (p = Position[ {b}, _?(proofValue[ #] === pending &), {1}, Heads -> False]) =!= {}
	]
findNextPendingSit[ ps_PRFSIT$, _List, pos_List] :=
	($selectedProofStep = id@ps; {ps, pos})
findNextPendingSit[ args___] := unexpected[ findNextPendingSit, {args}]
       	
replaceProofSit[ po_PRFOBJ$, pos_ -> p_PRFSIT$] :=
	(* 
	This is a special case needed when building up the initial proof object.
	It can happen that the initial PS consists of a TERMINALNODE$ (namely, if the proof succeeds immediately).
	Hence, we want to call replaceProofSit there in order to update the proof tree correspondingly.
	*)
	Module[ {},
		$lastVisitedNode = id@p;
		ReplacePart[ po, pos -> p]
	]
	
replaceProofSit[ po_PRFOBJ$, pos_ -> new:node_[___]] :=
	Module[{parentID = id@Extract[ po, pos], sub, selpos},
		sub = poToTree[ new];
		$TMAproofTree = Join[ $TMAproofTree /. {parentID, pending, PRFSIT$, None} -> {id@new, proofValue@new, node, name@new}, sub];
		$lastVisitedNode = id@new;
		(* 'new' might be free of PRFSIT$ *)
		If[ TrueQ[$interactiveProofSitSel] && (selpos = Position[ new, _PRFSIT$, Infinity, 1]) =!= {},
			$selectedProofStep = id[ Extract[ new, First[ selpos]]];
		];
		ReplacePart[ po, pos -> new]
	]
replaceProofSit[ args___] := unexpected[ replaceProofSit, {args}]


(* ::Subsubsection:: *)
(* optComponent / isOptComponent *)

optComponents[ data___?OptionQ] :=
	Apply[ Sequence, DeleteDuplicates[ Select[ {data}, isOptComponent], #1[[1]] === #2[[1]]&]]
optComponents[ args___] := unexpected[ optComponents, {args}]

isOptComponent[ (Rule|RuleDelayed)[ _String, _]] := True
isOptComponent[ _] := False
isOptComponent[ args___] := unexpected[ isOptComponent, {args}]


(* ::Section:: *)
(* Proof simplification *)

(*
	simplifyProof[ PRFOBJ$[ pi_, sub_, proved], proofTree_, simp_List] simplifies the proof object and
	   the corresponding tree representation according to the settings given in simp
	   and saves the respective proof object and the corresponding tree representation in a file.
*)
simplifyProof[ PRFOBJ$[ pi_, sub_, pv_], pt_, simp_List /; Apply[ Or, simp], file_String] := 
(*	
	We call the function only if at least one of the simplification settings is True
*)
	Module[{simpPo, sn, used, spi, startTime = SessionTime[], endTime, simpPt},
		{sn, used} = simpNodes[ sub, simp];
		If[ simp[[3]] && used =!= {}, (* used=={} indicates that only failing branches are there *)
			(* simplify formulae *)
			spi = eliminateUnusedInit[ pi, used];
			simpPo = PRFOBJ$[ spi, sn, pv],
			(* else *)
			simpPo = PRFOBJ$[ pi, sn, pv]
		];
		endTime = SessionTime[];
		(* Time for simplification does not include time for generating visual tree representation and time for file output *)
		simpPt = poToTree[ simpPo];
		Put[ {simpPo, simpPt, endTime-startTime}, simpPoFilename[ file, simp]];
		{simpPo, simpPt}
	]
simplifyProof[ po_PRFOBJ$, pt_, simp_List, file_String] := {po, pt}
simplifyProof[ args___] := unexpected[ simplifyProof, {args}]

simpPoFilename[ file_String, simp_List] :=
	Module[{sExt},
		sExt = FromDigits[ simp /. {True -> 1, False -> 0}, 2];
		simpPoFilename[ file, sExt]
	]
simpPoFilename[ file_String, 0] := file <> "-po" <> ".m"
simpPoFilename[ file_String, sExt_Integer?Positive] := file <> "-po-" <> ToString[ sExt] <> ".m"
simpPoFilename[ args___] := unexpected[ simpPoFilename, {args}]


(*
	simpNodes[ tree] computes {simpTree, used}, where
		simpTree is the simplified proof tree and
		used is a list of formula keys that are used within the simplified tree
*)

(* 
    ORNODEs originating from alternative proof rules to be applied should be removed completely.
*)
simpNodes[ ORNODE$[ pi_ /; name@pi === proofAlternatives, ___, p_ /; proofValue@p === proved, ___, proved], simp:{True, _, _}] :=
	simpNodes[ p, simp]
(* 
    ORNODEs originating from a proof rule, which introduced an OR-alternative explicitly typically simplify to an ANDNODE containing
    the successful branch from the ORNODE. Typically, there will be only one successful branch, in any case, we take the first one.
*)
simpNodes[ ORNODE$[ pi_, pre___, p_ /; proofValue@p === proved, ___, proved], simp:{True, _, _}] :=
	simpNodes[ ANDNODE$[ simplifiedProofInfo[ pi, Length[{pre}] + 1], p, proved], simp]
simpNodes[ ORNODE$[ pi_, a___, p_ /; proofValue@p === proved, b___, proved], simp:{False, _, _}] :=
	Module[{sn, used},
		{sn, used} = simpNodes[ p, simp];
		{ORNODE$[ pi, a, sn, b, proved], used}
	]
simpNodes[ node_ORNODE$, simp_] := {node, {}}

(* AndNode with only one successor *)
simpNodes[ ANDNODE$[ pi_, sub_, proved], simp:{sBranches_, sSteps_, sFormulae_}] :=
	Module[{sn, u, propUsed, thinnedGenerated, allUsed},
		{sn, u} = simpNodes[ sub, simp];
		propUsed = propagateUsed[ pi, u];
		allUsed = DeleteDuplicates[ Join[ u, propUsed]];
		Which[
			sSteps && propUsed === {}, (* eliminate whole step *)
			{sn, u},
			sFormulae, (* eliminate unused formulae *)
			thinnedGenerated = eliminateUnused[ pi, u];
			{ANDNODE$[ thinnedGenerated, sn, proved], allUsed},
			True,
			{ANDNODE$[ pi, sn, proved], allUsed}
		]
	]
simpNodes[ node:ANDNODE$[ pi_, sub_, pv_], simp_] := {node, {}}

(*
	AndNode (proved) with more than one successor: if the generated formulae are not used afterwards, the
	node can be substituted by one of its successful successors, e.g. the first one
*)
simpNodes[ ANDNODE$[ pi_, fsub_, rsub__, pv_], simp:{sBranches_, sSteps_, sFormulae_}] :=
	Module[{sn, u, allUsed, propUsed},
		{sn, u} = Transpose[ Map[ simpNodes[ #, simp]&, {fsub, rsub}]];
		allUsed = Apply[ Union, u];
		propUsed = propagateUsed[ pi, allUsed];
		If[ (sBranches || sSteps) && propUsed === {},
			(* No formula used in the subproofs has been generated in this step: we eliminate the node and use the first successor node instead *)
			{sn[[1]], u[[1]]},
			(* Otherwise, we collect the simplified subproofs and union the keys used in this step to those used in the successors *)
			{Apply[ ANDNODE$[ pi, ##, pv]&, sn], Union[ propUsed, allUsed]}
		]		
	]
simpNodes[ node:TERMINALNODE$[ pi_, pv_], simp_List] := {node, Map[ key, Flatten[ used@pi]]}
simpNodes[ node:PRFSIT$[ g_, kb_, ___], simp_List] := {node, Map[ key, Prepend[ kb, g]]}
simpNodes[ args___] := unexpected[ simpNodes, {args}]

(*
	propagateUsed[ pi_PRFINFO$, u_List] computes a list of keys, which are used to generate all the keys in u.
	This is used in the proof simplification of a node having prfinfo pi: u are the keys used in the subproofs.
	We check, which of them are generated in the current step and collect the keys used to generate these.
	Finally take the union of all these.
*)
propagateUsed[ pi_PRFINFO$, u_List] :=
	Module[{gen = generated@pi, pUsed},
		(* The first entry in the position lists tells, in which component the formula is generated *)
		pUsed = Map[ Take[ #, 1]&, DeleteCases[ Map[ Position[ gen, #]&, u], {}], {2}];
		(* Extract the respective positions from used to get all formulae used and form their union *)
		DeleteDuplicates[ Map[ key, Flatten[ Extract[ used@pi, pUsed]]]]
	]
propagateUsed[ args___] := unexpected[ propagateUsed, {args}]

(* 
	Eliminate unused formulae from generated formulae
*)
eliminateUnused[ pi_PRFINFO$, u_List] :=
	Module[{gen = generated@pi, thinned, p},
		thinned = DeleteCases[ gen, _?(!MemberQ[ u, key[#]]&), {2}];
		p = Position[ thinned, {}];
		ReplacePart[ pi, {2 -> Delete[ used@pi, p], 3 -> Delete[ thinned, p]}]
	]
eliminateUnused[ args___] := unexpected[ eliminateUnused, {args}]

(* 
	Eliminate unused formulae from initial KB (the first one, i.e. the goal, must never be deleted).
*)
eliminateUnusedInit[ pi_PRFINFO$, used_List] :=
	Module[{gen = generated@pi, thinnedKB},
		thinnedKB = DeleteCases[ Rest[ gen[[1]]], _?(!MemberQ[ used, key[#]]&)];
		ReplacePart[ pi, 3 -> {Prepend[ thinnedKB, gen[[1, 1]]]}]
	]
eliminateUnusedInit[ args___] := unexpected[ eliminateUnusedInit, {args}]

(* ::Section:: *)
(* Proof object data structures *)


(* ::Subsection:: *)
(* PRFSIT$ *)

(*
  PRFSIT$[ goal_FML$, kb_List, id_String, addInfo___?OptionQ], where

	addInfo consists of required fields (in this order):
	rules->...  for the collection of proof rules to be used,
	ruleActivity->... for a list representing the rules' activity,
	rulePriority->... for a list representing the rules' priorities,
	strategy->... for the strategy to be used,
	kbRules->... for rewrite rules for the kb,
	goalRules->... for rewrite rules for the goal,
	substRules->... for elementary substitution rules,
	defRules->... for definition rewrite rules.
	
	In addition, there are optional fields
  	"key"-> for arbitrary strings "key" (the datastructure can be expanded by additional components of this type at any time)
  	
	The constructor understands options goal->, kb->, id->, rules->, ruleActivity->, rulePriority->, strategy->, 
		kbRules->, goalRules->, substRules->, defRules->, and "key"-> (for an arbitrary string "key").
*)

Options[ makePRFSIT] = {goal :> makeFML[], kb -> {}, id :> ToString[ Unique[ "PRFSIT$"]], rules -> Hold[], ruleActivity -> {}, rulePriority -> {}, strategy -> Identity,
	kbRules -> {}, goalRules -> {}, substRules -> {}, defRules -> {}};
makePRFSIT[ data___?OptionQ] :=
	Module[{g, k, i, r, a, p, s, kr, gr, sr, dr},
		{g, k, i, r, a, p, s, kr, gr, sr, dr} = 
			{goal, kb, id, rules, ruleActivity, rulePriority, strategy, kbRules, goalRules, substRules, defRules} /. {data} /. Options[ makePRFSIT];
		If[ TrueQ[ $autoGenerateRules],
			(* We consider $rewriteRules only if automatic generation of rewrite rules is activated. 
				Otherwise $rewriteRules would be {} and the Join operation below would be void, thus we save this useless computation. *)
			Assert[ MatchQ[ $rewriteRules, _List]];
			{kr, gr, sr, dr} = MapThread[ Join, Append[ $rewriteRules, {kr, gr, sr, dr}]]
		];
		PRFSIT$[ g, k, i, rules -> r, ruleActivity -> a, rulePriority -> p, strategy -> s,
			kbRules -> kr, goalRules -> gr, substRules -> sr, defRules -> dr,
			optComponents[ data]]
	]
makePRFSIT[ args___] := unexpected[ makePRFSIT, {args}]

goal[ PRFSIT$[ g_FML$, _, _, ___]] := g
goal[ args___] := unexpected[ goal, {args}]

kb[ PRFSIT$[ _, k_List, _, ___]] := k
kb[ args___] := unexpected[ kb, {args}]

id[ PRFSIT$[ _, _, i_String, ___]] := i
(* default rule follows below, because we have id also for other datastructures *)

rules[ PRFSIT$[ _, _, _, ___, rules -> Hold[ r_], ___]] := r
rules[ args___] := unexpected[ rules, {args}]

ruleActivity[ PRFSIT$[ _, _, _, ___, (Rule|RuleDelayed)[ ruleActivity, val_], ___]] := val
ruleActivity[ args___] := unexpected[ ruleActivity, {args}]

rulePriority[ PRFSIT$[ _, _, _, ___, (Rule|RuleDelayed)[ rulePriority, val_], ___]] := val
rulePriority[ args___] := unexpected[ rulePriority, {args}]

ruleSetup[ ps_PRFSIT$] := {rules@ps, ruleActivity@ps, rulePriority@ps}
ruleSetup[ args___] := unexpected[ ruleSetup, {args}]

strategy[ PRFSIT$[ _, _, _, ___, (Rule|RuleDelayed)[ strategy, val_], ___]] := val
strategy[ args___] := unexpected[ strategy, {args}]

kbRules[ PRFSIT$[ _, _, _, ___, (Rule|RuleDelayed)[ kbRules, val_], ___]] := val
kbRules[ args___] := unexpected[ kbRules, {args}]

goalRules[ PRFSIT$[ _, _, _, ___, (Rule|RuleDelayed)[ goalRules, val_], ___]] := val
goalRules[ args___] := unexpected[ goalRules, {args}]

substRules[ PRFSIT$[ _, _, _, ___, (Rule|RuleDelayed)[ substRules, val_], ___]] := val
substRules[ args___] := unexpected[ substRules, {args}]

defRules[ PRFSIT$[ _, _, _, ___, (Rule|RuleDelayed)[ defRules, val_], ___]] := val
defRules[ args___] := unexpected[ defRules, {args}]

proofValue[ _PRFSIT$] := pending
(* default rule follows below, because we have proofValue also for other datastructures *)

(* ::Subsection:: *)
(* toBeProved *)

Options[ toBeProved] = Options[ makePRFSIT];
toBeProved[ data___?OptionQ] := checkProofSuccess[ makePRFSIT[ data]]
toBeProved[ args___] := unexpected[ toBeProved, {args}]

checkProofSuccess[ ps_PRFSIT$] /; $TMAcheckSuccess := 
	Module[{termRules = getActiveRulesType[ ps, "term"]}, 
		Replace[ ps, termRules]
	]
checkProofSuccess[ ps_PRFSIT$] := ps
checkProofSuccess[ args___] := unexpected[ checkProofSuccess, {args}]



(* ::Subsection:: *)
(* PRFINFO$ *)

(*
  PRFINFO$[ name_, used_List, generated_List, id_String, addInfo___?OptionQ]
  
	The consturctor understands options name->, used->, generated->, id->, and "key"-> (for an
  	arbitrary string "key").

    Inside an ANDNODE:
  	used and generated are list of lists {u_1,...,u_n} and {g_1,...,g_n} such that the formulas
  	in u_i are those used to generate those in g_i.
  	
  	Inside an ORNODE:
  	used and generated are lists {u_1,...,u_n} and {g_1,...,g_n} such that u_i and g_i
  	are the used and generated lists for the i-th child of the node. The structure of the
  	u_i and g_i is as described for ANDNODEs.
*)

Options[ makePRFINFO] = {name -> "???", used -> {}, generated :> $generated, id -> ""};
makePRFINFO[ data___?OptionQ] :=
	Module[{n, u, g, i},
		{n, u, g, i} = {name, used, generated, id} /. {data} /. Options[ makePRFINFO];
		makeRealPRFINFO[ n, u, g, i, optComponents[ data]]
	]
makePRFINFO[ args___] := unexpected[ makePRFINFO, {args}]

makeRealPRFINFO[ name_, u_FML$, g_, id_String, rest___?OptionQ] := makeRealPRFINFO[ name, {{u}}, g, id, rest]
makeRealPRFINFO[ name_, u_, g_FML$, id_String, rest___?OptionQ] := makeRealPRFINFO[ name, u, {{g}}, id, rest]
makeRealPRFINFO[ name_, {u__FML$}, g_, id_String, rest___?OptionQ] := makeRealPRFINFO[ name, {{u}}, g, id, rest]
makeRealPRFINFO[ name_, u_, {g__FML$}, id_String, rest___?OptionQ] := makeRealPRFINFO[ name, u, {{g}}, id, rest]
makeRealPRFINFO[ name_, u:{___List}, g:{___List}, "", rest___?OptionQ] := PRFINFO$[ name, u, g, ToString[ Unique[ name]], rest]
makeRealPRFINFO[ name_, u:{___List}, g:{___List}, id_String, rest___?OptionQ] := PRFINFO$[ name, u, g, id, rest]
makeRealPRFINFO[ args___] := unexpected[ makeRealPRFINFO, {args}]

name[ PRFINFO$[ n_, _, _, _, ___]] := n
used[ PRFINFO$[ _, u_List, _, _, ___]] := u
generated[ PRFINFO$[ _, _, g_List, _, ___]] := g
id[ PRFINFO$[ _, _, _, i_String, ___]] := i


(* ::Subsection:: *)
(* Proof nodes *)

isProofNode[ obj_] := MatchQ[ obj, _ANDNODE$|_ORNODE$|_TERMINALNODE$]
isProofNode[ args___] := unexpected[ isProofNode, {args}]

makeTERMINALNODE[ pi_PRFINFO$, v:(failed|proved|disproved)] := TERMINALNODE$[ pi, v]
makeTERMINALNODE[ args___] := unexpected[ makeTERMINALNODE, {args}]

proofDisproved[ pi_PRFINFO$] := TERMINALNODE$[ pi, disproved]
proofDisproved[ args___] := unexpected[ proofDisproved, {args}]

type[ node_?isProofNode] := Head[ node]
type[ args___] := unexpected[ type, {args}]

id[ node_?isProofNode] := id[ First[ node]] (* id of node is id of its PRFINFO *)
id[ args___] := unexpected[ id, {args}]

name[ node_?isProofNode] := name[ First[ node]]
name[ args___] := unexpected[ name, {args}]

SetAttributes[ used, Listable]
used[ node_?isProofNode] := used@node[[1]]
used[ args___] := unexpected[ used, {args}]

SetAttributes[ generated, Listable]
generated[ node_?isProofNode] := generated@node[[1]]
generated[ args___] := unexpected[ generated, {args}]

proofValue[ node_?isProofNode] := Last[ node]
proofValue[ po_PRFOBJ$] := Last[ po]
proofValue[ args___] := unexpected[ proofValue, {args}]

branches[ _[ _PRFINFO$, subnodes___, _]] := {subnodes}
branches[ args___] := unexpected[ branches, {args}]

makeANDNODE[ pi_PRFINFO$, subnode_] := ANDNODE$[ pi, subnode, pending]
makeANDNODE[ pi_PRFINFO$, {subnodes__}] := ANDNODE$[ pi, subnodes, pending]
makeANDNODE[ args___] := unexpected[ makeANDNODE, {args}]

makeORNODE[ pi_PRFINFO$, {subnodes__}] := ORNODE$[ pi, subnodes, pending]
makeORNODE[ args___] := unexpected[ makeORNODE, {args}]

poToTree[ _TERMINALNODE$|_PRFSIT$] := {}
poToTree[ node_[ pi_PRFINFO$, sub___, val_]] :=
	Module[{root, subTrees, topLevel},
		root = {id@pi, val, node, name@pi};
		subTrees = Flatten[ Map[ poToTree, {sub}]];
		topLevel = Map[ (root -> poNodeToTreeNode[#])&, {sub}];
		Join[ topLevel, subTrees]
	]
poToTree[ args___] := unexpected[ poToTree, {args}]

poNodeToTreeNode[ ps_PRFSIT$] := {id@ps, pending, PRFSIT$, None}
poNodeToTreeNode[ node_[ pi_PRFINFO$, ___, val_]] := {id@pi, val, node, name@pi}
poNodeToTreeNode[ args___] := unexpected[ poNodeToTreeNode, {args}]

propagateProofValues[ poNode:node_[ pi_PRFINFO$, subnodes__, pending]] :=
	Module[ {updSub, subVal, newVal},
		updSub = Map[ propagateProofValues, {subnodes}];
		subVal = Map[ proofValue, updSub];
		newVal = nodeValue[ node, subVal];
		If[ newVal =!= pending,
			$TMAproofTree = With[ {id = id@pi},
				$TMAproofTree /. {id, pending, t_, n_} -> {id, newVal, t, n}
			]
		];
		node[ pi, Apply[ Sequence, updSub], newVal]
	]
propagateProofValues[ node_] := node
propagateProofValues[ args___] := unexpected[ propagateProofValues, {args}]

nodeValue[ ANDNODE$, {___, failed, ___}] := failed
nodeValue[ ANDNODE$, { proved..}] := proved
nodeValue[ ANDNODE$, {___, disproved, ___}] := disproved
nodeValue[ ANDNODE$, _List] := pending
nodeValue[ ORNODE$, {___, proved, ___}] := proved
nodeValue[ ORNODE$, { failed..}] := failed
nodeValue[ ORNODE$, { disproved..}] := disproved
nodeValue[ ORNODE$, _List] := pending
nodeValue[ PRFOBJ$, {v_}] := v
nodeValue[ args___] := unexpected[ nodeValue, {args}]

searchDepthExceeded[ ps_PRFSIT$] := makeTERMINALNODE[ makePRFINFO[ name -> searchDepthLimit, used -> {Apply[ List, ps]}, id -> id@ps], failed]
searchDepthExceeded[ args___] := unexpected[ searchDepthExceeded, {args}]

noProofNode[ expr_, i_] := makeTERMINALNODE[ makePRFINFO[ name -> invalidProofNode, used -> {expr}, id -> i], failed]
noProofNode[ args___] := unexpected[ noProofNode, {args}]


(* ::Subsubsection:: *)
(* getActiveRules *)

(*
	If op =!= Flatten, i.e. we keep a structured list of rules, we need to clarify the role of rulePriority, maybe sort sublists recursively? *)
getActiveRulesFilter[ ps_PRFSIT$, filter_, op_:Identity] := 
	Module[{rules, act, prio, names},
		(* Select names of active rules, delete rules of type filter, strings (category names) and inactive rules, finally apply op *)
		{rules, act, prio} = ruleSetup@ps;
		names = op[ rules /. {{r_, _, _, _Integer, filter} -> Sequence[],
			{r_ /; Replace[ r, act], _, _, _Integer, ___} -> r, _String | {r_Symbol, _, _, _Integer, ___} -> Sequence[]}];
		If[ Depth[ names] == 2,
			(* we have a flat list of rule names *)
			names = Sort[ DeleteDuplicates[ names], Replace[ #1, prio] < Replace[ #2, prio] &];
			DeleteCases[ Map[ inferenceRule, names], _inferenceRule],
			(* else *)
			DeleteCases[ MapAt[ inferenceRule, names, Position[ names, _Symbol, Heads -> False]], _inferenceRule, Infinity]
		]
	]	
getActiveRulesFilter[ args___] := unexpected[ getActiveRulesFilter, {args}]

getActiveRulesType[ ps_PRFSIT$, type_] :=
	Module[{rules, act, prio, names},
		(* Select flat list of names of active rules, delete strings (category names) and inactive rules *)
		{rules, act, prio} = ruleSetup@ps;
		names = Cases[ rules, {r_ /; Replace[ r, act], _, _, _Integer, type} -> r, Infinity];
		(* we have a flat list of rule names *)
		names = Sort[ DeleteDuplicates[ names], Replace[ #1, prio] < Replace[ #2, prio] &];
		DeleteCases[ Map[ inferenceRule, names], _inferenceRule]
	]
getActiveRulesType[ args___] := unexpected[ getActiveRulesType, {args}]


(* ::Subsubsection:: *)
(* applyAllRules *)

applyAllRules[ ps_PRFSIT$, rules_List] :=
	DeleteCases[ ReplaceList[ ps, rules], $Failed]
applyAllRules[ args___] := unexpected[ applyAllRules, {args}]


(* ::Subsubsection:: *)
(* showProofNavigation *)

showProofNavigation[ {}, scale_, maxDepth_, mode_] := Graphics[ {}, ImageSize -> {350,420}]

(*
The initial proof tree already has an edge from original PS to initial PS, so this should not be called anymore

showProofNavigation[ {Depth -> _, node_List}, scale_] := Graphics[ proofStepNode[ {0, 0}, node, 18], ImageSize -> {350,420}, PlotRegion -> {{0.4, 0.6}, {0.6, 0.8}}]
*)

showProofNavigation[ p:{__Rule}, scale_, maxDepth_, mode_] :=
    Module[ {edges, root, geometry, font, framed},
    	Switch[ mode,
    		All,
    		edges = p;
    		root = Cases[ p, {"OriginalPS", __}, {2}];
    		framed = False,
    		Automatic,
    		{edges, root} = zoomedTree[ p];
    		framed = True;
    	];
    	If[ scale === Fit,
    		geometry = {350,500},
    		(* else *)
    		geometry = {Max[ Count[ p, _ -> {__, TERMINALNODE$|PRFSIT$, _}]*20, 350], Max[ $TMAcurrentDepth*15, 500]}*scale
    	];
    	font = 18-Ceiling[ Apply[ Times, geometry]/(350*500)];
        If[ root === {},
            translate[ "noRoot"],
            TreePlot[ edges, Automatic, First[ root], VertexRenderingFunction -> (proofStepNode[ #1, #2, font]&),
            EdgeRenderingFunction -> ({Dashed, GrayLevel[0.5], Line[#1]}&), ImageSize -> geometry, 
            AspectRatio -> If[ MatchQ[ edges, {___, a_ -> _, a_ -> _, ___}], (* branching tree *) 1/Apply[ Divide, geometry], (* non-branching chain *) Automatic],
            Frame -> framed, FrameStyle -> Dotted]
        ]
    ]
showProofNavigation[ args___] := unexpected[ showProofNavigation, {args}]

zoomedTree[ p_List] :=
	Module[{edges, nodes, root},
		nodes = NestList[ parentNode[#, p] &, $lastVisitedNode, 5];
		edges = Cases[ p, HoldPattern[{id_, __} /; MemberQ[ nodes, id] -> _]];
		root = Cases[ p, HoldPattern[n:{id_, __} /; id === Last[ nodes] -> _] -> n, {1}, 1];
		{edges, root}
	]
zoomedTree[ args___] := unexpected[ zoomedTree, {args}]

parentNode[ id_, {___, {p_, __} -> {id_, __}, ___}] := p
parentNode[ id_, T_] := id
parentNode[ args___] := unexpected[ parentNode, {args}]

proofStepNode[ pos_List, node:{ id_String, status_, type_, name_}, font_] := 
	Module[{opacity = If[ TrueQ[ ruleTextActive[ name]], 1, 0.3], selectionMarker},
		If[ id === $selectedProofStep,
			selectionMarker = {Text[ "\[LeftPointer]", pos + {0.1,0}, {-1,0}]},
			selectionMarker = {}
		];
		Join[ selectionMarker,
			{
			If[ id === $lastVisitedNode,
				Yellow,
				(* else *)
				Switch[ status,
					pending, RGBColor[0.360784, 0.67451, 0.933333, opacity] (* steelblue *),
					failed, RGBColor[1, 0.270588, 0, opacity] (* orangered *),
					proved, RGBColor[0, 0.780392, 0.54902, opacity] (* turquoiseblue *),
					_, Black]
			],
			Switch[ type,
				PRFSIT$|PRFOBJ$, Disk[ pos, 0.1],
				TERMINALNODE$, Map[ (pos + 0.1*#)&, Rectangle[ {-Sqrt[Pi]/2, -Sqrt[Pi]/2}, {Sqrt[Pi]/2, Sqrt[Pi]/2}]],
				ANDNODE$, Polygon[ Map[ (pos + 0.125*#)&, {{0,1}, {Cos[7*Pi/6], Sin[7*Pi/6]}, {Cos[11*Pi/6], Sin[11*Pi/6]}}]],
				ORNODE$, Polygon[ Map[ (pos + 0.125*#)&, {{0,-1}, {Cos[Pi/6], Sin[Pi/6]}, {Cos[5*Pi/6], Sin[5*Pi/6]}}]],
				_, Map[ (pos + 0.1*#)&, Rectangle[ {-Sqrt[Pi]/2, -Sqrt[Pi]/2}, {Sqrt[Pi]/2, Sqrt[Pi]/2}]]],
			{Black, Dynamic[ Text[ EventHandler[
				Hyperlink[
					Switch[ type, 
        				TERMINALNODE$, proofStatusIndicator[ status, name],
         				PRFOBJ$, proofStatusIndicator[ status],
       					_, proofNodeIndicator[ status, type, name]], 
					{$TMAproofNotebook, id},
					BaseStyle -> {FontSize -> font}, Active -> ValueQ[ $TMAproofNotebook] && ruleTextActive[ name]],
					{"MouseClicked" :> If[ !TrueQ[ $interactiveProofSitSel] || type === PRFSIT$, $selectedProofStep = id]}, PassEventsDown -> True], pos]]}
			}
		]
	]
proofStepNode[ args___] := unexpected[ proofStepNode, {args}]

proofStatusIndicator[ status_] :=
    Style[
        Switch[ status, 
            proved, "\[CheckmarkedBox]",
        	disproved, "\[Times]",
        	failed, "\[WarningSign]",
        	pending, "?",
        	_, "\[DownQuestion]"
    	], ShowStringCharacters -> False
    ]
	
proofStatusIndicator[ status_, name_] := Tooltip[
	Switch[ name,
		searchDepthLimit, "\[Ellipsis]",
		noApplicableRule, "\[Dagger]",
		_, proofStatusIndicator[ status]
	],
	translate[ SymbolName[ status]] <> If[ status =!= pending, " (" <> MessageName[ name, "usage", $TmaLanguage] <> ")", ""]]
	
proofStatusIndicator[ args___] := unexpected[ proofStatusIndicator, {args}]

proofNodeIndicator[ status_, type_, name_] :=
	Module[ {label, description},
		{label, description} = Switch[ type,
			PRFSIT$, {"\[Paragraph]", translate[ "open proof situation"]},
        	ANDNODE$, {"\[Wedge]", MessageName[ name, "usage", $TmaLanguage]},
        	ORNODE$, {"\[Vee]", MessageName[ name, "usage", $TmaLanguage]},
        	_, {"\[DownQuestion]", translate[ "unknown proof node"]}
		];
		Tooltip[ Style[ label, ShowStringCharacters -> False], description <> " (" <> translate[ SymbolName[ status]] <> ")"]
	]
proofNodeIndicator[ args___] := unexpected[ proofNodeIndicator, {args}]

(* ::Subsubsection:: *)
(* makeInitialProofObject *)

makeInitialProofObject[ g_FML$, k_List, {r_Hold, act_List, prio_List}, s_] :=
    Module[ {dummyPO, simpG = computeInProof[ g], simpK = Map[ With[ {new = computeInProof[ #]}, If[ new === $Failed, #, new]]&, k], thinnedKB, dr, sr, gr, kr, const},
    	If[ simpG === $Failed, simpG = g];
        dummyPO = PRFOBJ$[
            makePRFINFO[ name -> initialProofSituation, generated -> Prepend[ simpK, simpG], id -> "OriginalPS"],
            PRFSIT$[ simpG, simpK, "InitialPS"],
            pending
        ];
        (* Use propagateProofValues and replaceProofSit in order to update the proof tree correspondingly *)
        (* Handling of substitutions: from k we generate transformation rules relating to
        	"elementary substitutions", i.e. equalities or equivalences that do not introduce (logical) quantifiers,
        	"definitions", i.e. equalities or equivalences that normally do introduce quantifiers on the rhs,
        	"goal rewriting",
        	"kb rewriting".
           We put the generated rules into the respective components in the proof object. We don't put the original formulae corresponding to definitions and
           elementary substitutions into the KB then *)
        (* We try to figure out all constants available in the formulas *)
        const = guessConstants[ Append[ simpK, simpG]];
        If[ const =!= {},
        	(* Mark the constants as new *)
        	const = {Map[ SIMPRNG$, Apply[ RNG$, const]]}
        ];        	
        {thinnedKB, kr, gr, sr, dr} = trimKBforRewriting[ simpK];
        propagateProofValues[ 
            replaceProofSit[ dummyPO,
            	{2} -> toBeProved[ goal -> simpG, kb -> thinnedKB, id -> "InitialPS",
                		rules -> r, ruleActivity -> act, rulePriority -> prio, strategy -> s,
                		substRules -> sr, defRules -> dr, kbRules -> kr, goalRules -> gr, "constants" -> const]
            ]
        ]
    ]
makeInitialProofObject[ args___] := unexpected[ makeInitialProofObject, {args}]

guessConstants[ expr_] :=
	Module[ {hiddenSpecials, objConst},
		(* PREDRNG$ contains the predicate at Level -1 (as leaf). Not excluding PREDRNG$ would give those, and they would be 
			used for instanciation of variables *)
		hiddenSpecials = expr /. {_VAR$ -> "", _META$ -> "", _PREDRNG$ -> "", True|False -> ""};
		objConst = DeleteDuplicates[ Cases[ Level[ hiddenSpecials, {-1}], _Symbol | _?NumberQ]];
        Join[ objConst, DeleteDuplicates[ Cases[ hiddenSpecials, _SEQ0$|_SEQ1$|_FIX$, Infinity]]]
	]
guessConstants[ args___] := unexpected[ guessConstants, {args}]


(* ::Subsubsection:: *)
(* makeInitialProofTree *)

makeInitialProofTree[ ] := {{"OriginalPS", pending, PRFOBJ$, None} -> {"InitialPS", pending, PRFSIT$, None}}
makeInitialProofTree[ args___] := unexpected[ makeInitialProofTree, {args}]

(* ::Subsubsection:: *)
(* displayProof *)

displayProof[ file_String] :=
	Module[ {po, pt, st, cells},
		{po, pt, st} = getProofObjectTreeTime[ file];
		cells = proofObjectToCell[ po];
		$TMAproofObject = po;
		$TMAproofTree = pt; 
		$TMAproofNotebook = tmaNotebookPut[ Notebook[ cells], "Proof"];
		$selectedProofStep = "OriginalPS";
		With[ {nb = $TMAproofNotebook, tr = pt, obj = po},
			SetOptions[ $TMAproofNotebook, NotebookEventActions -> {{"KeyDown", "r"} :> ($TMAproofNotebook = nb; $TMAproofObject = obj; $TMAproofTree = tr;),
				"WindowClose" :> ($TMAproofTree = {};), PassEventsDown -> False}]
		];
	]
displayProof[ file_String, simp_List] :=
	Module[ {fspo, po, pt, st, cells, newDock, tmp, favIcon},
		If[ !ValueQ[ origDock],
			origDock = DockedCells /. Options[ tmp = NotebookPut[ Notebook[ {}], StyleDefinitions -> makeColoredStylesheet[ "Proof"], Visible -> False], DockedCells];
			NotebookClose[ tmp];
		];
		If[ FileExistsQ[ fspo = simpPoFilename[ file, simp]],
			{po, pt, st} = getProofObjectTreeTime[ fspo],
			(* else *)
			{po, pt, st} = getProofObjectTreeTime[ simpPoFilename[ file, 0]];			
		];
		cells = proofObjectToCell[ po];
		$TMAproofObject = po;
		$TMAproofTree = pt; 
		{$eliminateBranches, $eliminateSteps, $eliminateFormulae} = simp;
		If[ Apply[ Or, simp],
			favIcon = MouseAppearance[ EventHandler[ Dynamic[ Refresh[ showFavIcon[ file, simp], UpdateInterval -> 1]], 
								{"MouseClicked" :> toggleFavIcon[ file, simp]}],
							"Arrow"],
			favIcon = ""
		];
		newDock = {origDock, 
  			Cell[ BoxData[ ToBoxes[ OpenerView[ {Grid[ {{Item[ Style[ translate[ "pSimp"], "Subsubsection"], ItemSize -> Scaled[0.46], Alignment -> Left],
  				Item[ Tooltip[ favIcon, translate[ "Mark favourite"], PassEventsDown -> True], ItemSize -> Scaled[0.08], Alignment -> Center], 
  				Item[ If[ st > 0, 
  					     Style[ translate[ "proofSimpTime"] <> ": " <> If[ Negative[ st], "\[LongDash]", ToString[ st]] <> "s", "SmallText"],
  					     (* else *)
  					     ""], ItemSize -> Scaled[0.46], Alignment -> Right]}}], 
       			Column[ {Grid[{
    				{Checkbox[ Dynamic[ $eliminateBranches]], Style[ translate[ "elimBranches"] <> If[ simp[[1]], " \[Checkmark]", ""], "Text"]},
    				{Checkbox[ Dynamic[ $eliminateSteps]], Style[ translate[ "elimSteps"] <> If[ simp[[2]], " \[Checkmark]", ""], "Text"]},
    				{Checkbox[ Dynamic[ $eliminateFormulae]], Style[ translate[ "elimForm"] <> If[ simp[[3]], " \[Checkmark]", ""], "Text"]}
    				}, Alignment -> {Left}], 
    				Button[ translate[ "Display with new settings"], 
    					displaySimplified[ file, {$eliminateBranches, $eliminateSteps, $eliminateFormulae}, ButtonNotebook[]], Method -> "Queued"]}]},
    			Spacings -> {0.8, Automatic}]]], "SimplificationDock", Background -> TMAcolor[ 8, $TheoremaColorScheme]]};
		$selectedProofStep = "OriginalPS";
		(* If[ ValueQ[ oldNb], NotebookClose[ oldNb]];*)
		With[ {tr = pt, obj = po},
		    $TMAproofNotebook = tmaNotebookPut[ Notebook[ cells], "Proof",
		    	NotebookEventActions -> {{"KeyDown", "r"} :> ($TMAproofNotebook = SelectedNotebook[]; $TMAproofObject = obj; $TMAproofTree = tr;),
										  PassEventsDown -> False, "WindowClose" :> ($TMAproofTree = {};)},
				DockedCells -> newDock]
		]
	]
displayProof[ args___] := unexpected[ displayProof, {args}]

displaySimplified[ file_String, simp_List, origNb_NotebookObject] /; Apply[ Or, simp]:=
	Module[ {fpo = file <> "-po.m", fspo = simpPoFilename[ file, simp], po, pt, st},
		If[!FileExistsQ[ fspo] || AbsoluteTime[ FileDate[ fspo]] < AbsoluteTime[ FileDate[ fpo]],
			(* if a simplified proof does not yet exist or the full proof object is newer than the existing simplified one: simplify *)
			{po, pt, st} = getProofObjectTreeTime[ fpo];
			{po, pt} = simplifyProof[ po, pt, simp, file]
		];
		NotebookClose[ origNb];
		displayProof[ file, simp]
	]
	
displaySimplified[ file_String, simp_List, origNb_NotebookObject] :=
	Module[ {},
		DeleteFile[ FileNames[ file <> "-po-*.m"]];
		NotebookClose[ origNb];
		displayProof[ file, simp]
	]
displaySimplified[ args___] := unexpected[ displaySimplified, {args}]

showFavIcon[ file_, simp_] := 
	Module[{}, 
		If[ FileExistsQ[ file <> "-po-fav.m"] && FromDigits[ simp /. {True -> 1, False -> 0}, 2] === Get[ file <> "-po-fav.m"], 
			Style[ "\[FivePointedStar]", FontSize -> 20, FontColor -> TMAcolor[ 7, $TheoremaColorScheme]], 
			Style[ "\:2606", FontSize -> 20, FontColor -> TMAcolor[ 13, $TheoremaColorScheme]]
		]
	]
showFavIcon[ args___] := unexpected[ showFavIcon, {args}]

toggleFavIcon[ file_, simp_] :=
	Module[{}, 
		If[ FileExistsQ[ file <> "-po-fav.m"] && FromDigits[ simp /. {True -> 1, False -> 0}, 2] === Get[ file <> "-po-fav.m"], 
			DeleteFile[ file <> "-po-fav.m"], 
			Put[ FromDigits[ simp /. {True -> 1, False -> 0}, 2], file <> "-po-fav.m"]
		]
	]
toggleFavIcon[ args___] := unexpected[ toggleFavIcon, {args}]

getProofObjectTreeTime[ file_String] :=
	Module[ {fileContent, po, pt, st=-1},
		fileContent = Get[ file];
		Switch[ fileContent,
			_PRFOBJ$,
			(* version 1 (until April 2017): file only contains the proof object *)
			po = fileContent;
			pt = poToTree[ po];
			Put[ {po, pt}, file],
			{_PRFOBJ$, _},
			(* version 2: file contains a list containing the proof object and the corresponding tree *)
			{po, pt} = fileContent,
			{_PRFOBJ$, _, _},
			(* file contains a list containing the proof object, the corresponding tree, and simplification time *)
			{po, pt, st} = fileContent;
		];
		{po, pt, st}
	]
getProofObjectTreeTime[ args___] := unexpected[ getProofObjectTreeTime, {args}]


(* ::Subsubsection:: *)
(* proofObjectToCell *)

(* 
	If proof text is deactivated, the result is {}. Proof texts are composed in such a way that {} simply cancels out and therfore no text appears.
*)
proofObjectToCell[ PRFOBJ$[ pi_PRFINFO$, sub_, pVal_]] := 
	Module[ {cellList = proofObjectToCell[ pi, pVal]},
		Join[ cellList, {proofObjectToCell[ sub, pVal]}]
	]
proofObjectToCell[ PRFINFO$[ name_?ruleTextActive, u_, g_, id_String, rest___?OptionQ], pVal_] := proofStepTextId[ id, name, u, g, rest, pVal]
proofObjectToCell[ PRFINFO$[ _, _, _, _String, ___?OptionQ], _] := {}
proofObjectToCell[ ps:PRFSIT$[ g_FML$, kb_List, id_String, ___], pVal_] := Cell[ CellGroupData[ proofStepTextId[ id, openProofSituation, {Apply[ List, ps]}, {}],
																			cellStatus[ $proofCellStatus, pending, pVal]]]
proofObjectToCell[ (ANDNODE$|ORNODE$)[ pi_PRFINFO$, subnodes__, pVal_], overallVal_] := 
	Module[{header, sub = {}},
		header = proofObjectToCell[ pi, pVal];
		If[ Length[ {subnodes}] == 1,
			sub = {proofObjectToCell[ subnodes, pVal]},
			(* else *)
			sub = MapIndexed[ subProofToCell[ pi, #1, #2, pVal]&, {subnodes}]
		];
		If[ header === {},
			Apply[ Sequence, sub],
			(* else *)
			Cell[ CellGroupData[ Join[ header, sub], cellStatus[ $proofCellStatus, pVal, overallVal]]]
		]
	]
proofObjectToCell[ TERMINALNODE$[ pi_PRFINFO$, pVal_], overallVal_] := 
	Cell[ CellGroupData[ proofObjectToCell[ pi, pVal], cellStatus[ $proofCellStatus, pVal, overallVal]]]
	
proofObjectToCell[ args___] := unexpected[ proofObjectToCell, {args}]

subProofToCell[ PRFINFO$[ name_, used_List, gen_List, rest___], node_, pos_List, pVal_] :=
	Cell[ CellGroupData[ Join[ subProofHeaderId[ id@node, name, used, gen, rest, proofValue@node, pos], {proofObjectToCell[ node, proofValue@node]}], 
		cellStatus[ $proofCellStatus, proofValue@node, pVal]]]
subProofToCell[ args___] := unexpected[ subProofToCell, {args}]

cellStatus[ Automatic, pending, pending] := Open
cellStatus[ Automatic, _, pending] := Closed
cellStatus[ Automatic, _, failed] := Open
cellStatus[ Automatic, proved, proved] := Open
cellStatus[ Automatic, _, proved] := Closed
cellStatus[ Automatic, _, _] := Open
cellStatus[ Automatic, _] := Open
cellStatus[ v_, _, _] := v
cellStatus[ args___] := unexpected[ cellStatus, {args}]

(* pSitCells exported to be used in other places *)
pSitCells[ ps_PRFSIT$] := proofObjectToCell[ ps, pending]
pSitCells[ args___] := unexpected[ pSitCells, {args}]

(* pObjCells exported to be used in other places *)
pObjCells[ ] := pObjCells[ $TMAproofObject]
pObjCells[ po_PRFOBJ$] := proofObjectToCell[ po]
pObjCells[ args___] := unexpected[ pObjCells, {args}]


(* ::Section:: *)
(* Inference rule programming *)

SetAttributes[ performProofStep, HoldAll]

performProofStep[ prog_] :=
	Block[{$rewriteRules = {}, $generated = {}},
		Catch[ prog]
	]
performProofStep[ args___] := unexpected[ performProofStep, {args}]



(* ::Section:: *)
(* register provers *)

(*
  The list of rules 'l' has the format {l1, ..., ln}, where each li is either
  	o) a symbol standing for a previously defined rule list OR
  	o) a list {rulename, active, activeText, priority}, where
  		- rulename is the name of the rule,
  		- active is the default value for rule activation (True|False),
  		- activeText is the default value for proof text activation (True|False),
  		- priority is the default value for the rule priority (1-100).
*)
SetAttributes[ registerRuleSet, HoldAll]

registerRuleSet[ n_String, r_, l_List] := 
	Module[ {},
		$registeredRuleSets = Union[ $registeredRuleSets, {Hold[ r] -> n}];
		r = Prepend[ l, n];
	]
registerRuleSet[ args___] := unexpected[ registerRuleSet, {args}]

registerStrategy[ n_String, s_] := 
Module[ {},
		$registeredStrategies = Union[ $registeredStrategies, {s -> n}];
	]
registerStrategy[ args___] := unexpected[ registerStrategy, {args}]


(* ::Section:: *)
(* Package Initialization *)

initProver[]

End[]

EndPackage[]