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


(* ::Subsubsection:: *)
(* callProver *)

initProver[] :=
	Module[ {},
		(* $proofInProgressMarker is used in the docked cells in stylesheet for displaying proofs *)
		$proofInProgressMarker = {};
		$TMAproofTree = {};
		$registeredRuleSets = {};
		$registeredStrategies = {};
		Clear[ ruleTextActive];
		ruleTextActive[_] := True;
		$proofCellStatus = Open;
		$TMAcurrentDepth = 1;
	]

callProver[ ruleSetup:{_Hold, _List, _List}, strategy_, goal_FML$, kb_List, searchDepth_Integer] :=
	Module[{},
		$TMAcurrentDepth = 2;
		$TMAproofTree = makeInitialProofTree[ ];
		$TMAproofObject = makeInitialProofObject[ goal, kb, ruleSetup, strategy];
		$TMAproofNotebook = makeInitialProofNotebook[ $TMAproofObject];
		initFormulaLabel[];
		proofSearch[ searchDepth];
  		$proofInProgressMarker = {};
		{$TMAproofObject.proofValue, $TMAproofObject}
	]
callProver[ args___] := unexpected[ callProver, {args}]


(* ::Subsubsection:: *)
(* proofSearch *)

proofSearch[ searchDepth_Integer] :=
    Module[ {openPSpos, openPS, selPSpos, selPS, pStrat, newSteps},
    	$proofAborted = False;
        While[ !$proofAborted && $TMAproofObject.proofValue === pending && (openPSpos = positionRelevantSits[ $TMAproofObject]) =!= {},
            openPS = Extract[ $TMAproofObject, openPSpos];
            {selPS, selPSpos} = chooseNextPS[ openPS, openPSpos];
            $TMAcurrentDepth = Length[ selPSpos];
            If[ $TMAcurrentDepth > searchDepth,
            	newSteps = searchDepthExceeded[ selPS],
            	(* else *)
            	pStrat = selPS.strategy;
            	newSteps = pStrat[ selPS]
            ];
            If[ !isProofNode[ newSteps],
            	newSteps = noProofNode[ newSteps, selPS.id];
			];
            $TMAproofObject = replaceProofSit[ $TMAproofObject, selPSpos -> newSteps];
            $TMAproofObject = propagateProofValues[ $TMAproofObject];
        ]
    ]
proofSearch[ args___] := unexpected[ proofSearch, {args}]


(* ::Subsection:: *)
(* Experimental feature: prallel proof search *)

(* This needs more thoughts, how to update the proof tree when parallel modifications may take place.
   Just as a starting point ... *)
proofSearchParallel[ searchDepth_Integer] :=
    Module[ {openPSpos},
    	$proofAborted = False;
    	SetSharedVariable[$TMAproofObject, $TMAproofTree];
        While[ !$proofAborted && $TMAproofObject.proofValue === pending && (openPSpos = positionRelevantSits[ $TMAproofObject]) =!= {},
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
            pStrat = selPS.strategy;
            newSteps = pStrat[ selPS]
        ];
        If[ !isProofNode[ newSteps],
            newSteps = noProofNode[ newSteps, selPS.id];
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
			If[ (node.type === ANDNODE$ && node.proofValue === failed) ||
				(node.type === ORNODE$ && node.proofValue === proved),
				Return[ False]
			];
			path = Drop[ path, -1];
		];
		True
	]
stillRelevant[ args___] := unexpected[ stillRelevant, {args}]

chooseNextPS[ ps_List, psPos_List] :=
	Module[{},
		{First[ ps], First[ psPos]}
	]
chooseNextPS[ args___] := unexpected[ chooseNextPS, {args}]

replaceProofSit[ po_PRFOBJ$, pos_ -> p_PRFSIT$] :=
	(* 
	This is a special case needed when building up the initial proof object.
	It can happen that the initial PS consists of a TERMINALNODE$ (namely, if the proof succeeds immediately).
	Hence, we want to call replaceProofSit there in order to update the proof tree correspondingly.
	*)
	ReplacePart[ po, pos -> p]
	
replaceProofSit[ po_PRFOBJ$, pos_ -> new:node_[___]] :=
	Module[{parentID = Extract[ po, pos].id, newVal = new.proofValue, sub},
		sub = poToTree[ new];
		$TMAproofTree = Join[ $TMAproofTree /. {parentID, pending, PRFSIT$, None} -> {parentID, newVal, node, new.name}, sub];
		ReplacePart[ po, pos -> new]
	]
replaceProofSit[ args___] := unexpected[ replaceProofSit, {args}]


(* ::Subsection:: *)
(* isOptComponent *)

isOptComponent[ (Rule|RuleDelayed)[ _String, _]] := True
isOptComponent[ _] := False
isOptComponent[ args___] := unexpected[ isOptComponent, {args}]

(* ::Section:: *)
(* Proof object data structures *)


(* ::Subsection:: *)
(* PRFSIT$ *)

(*
  PRFSIT$[ goal_FML$, kb_List, id_String, addInfo___?OptionQ], where

	addInfo consists of required fields (in this order):
	local->...  for local proof info,
	rules->...  for the collection of proof rules to be used,
	ruleActivity->... for a list representing the rules' activity,
	rulePriority->... for a list representing the rules' priorities,
	strategy->... for the strategy to be used.
	
	In addition, there are optional fields
  	"key"-> for arbitrary strings "key" (the datastructure can be expanded by additional components of this type at any time)
  	
	The consturctor understands options goal->, kb->, local->, id->, rules->, ruleActivity->, rulePriority->, strategy->, and 
	"key"-> (for an arbitrary string "key").
  	The selectors for the datastructure are p.goal, p.kb, p.id, p.local, p.rules, p.ruleActivity, p.rulePriority, p.strategy, and p."key" (for an
  	arbitrary string "key"). The special selector p.ruleSetup is a combination of p.rules, p.ruleActivity, and p.rulePriority.
*)

Options[ makePRFSIT] = {goal -> {}, kb -> {}, id :> ToString[ Unique[ "PRFSIT$"]], local -> {}, rules -> Hold[], ruleActivity -> {}, rulePriority -> {}, strategy -> Identity};
makePRFSIT[ data___?OptionQ] :=
	Module[{g, k, i, l, r, a, p, s},
		{g, k, i, l, r, a, p, s} = {goal, kb, id, local, rules, ruleActivity, rulePriority, strategy} /. {data} /. Options[ makePRFSIT];
		PRFSIT$[ g, k, i, local -> l, rules -> r, ruleActivity -> a, rulePriority -> p, strategy -> s, Apply[ Sequence, Select[ {data}, isOptComponent]]]
	]
makePRFSIT[ args___] := unexpected[ makePRFINFO, {args}]

(*
	The selector p.rules immediately strips the Hold
*)
PRFSIT$ /: Dot[ PRFSIT$[ g_FML$, _, _, _, ___], goal] := g
PRFSIT$ /: Dot[ PRFSIT$[ _, k_List, _, _, ___], kb] := k
PRFSIT$ /: Dot[ PRFSIT$[ _, _, i_String, ___], id] := i
PRFSIT$ /: Dot[ PRFSIT$[ _, _, _, _, rules -> Hold[r_], ruleActivity -> act_, rulePriority -> prio_, ___], ruleSetup] := {r, act, prio}
PRFSIT$ /: Dot[ PRFSIT$[ _, _, _, _, rules -> Hold[r_], ___], rules] := r
PRFSIT$ /: Dot[ PRFSIT$[ _, _, _, ___, (Rule|RuleDelayed)[ key_, val_], ___], key_] := val
PRFSIT$ /: Dot[ _PRFSIT$, proofValue] := pending
PRFSIT$ /: Dot[ p_PRFSIT$, s___] := unexpected[ Dot, {p, s}]

getPrincipalData[ args___] := unexpected[ getPrincipalData, {args}]


(* ::Subsection:: *)
(* newSubgoal *)

Options[ newSubgoal] = Options[ makePRFSIT];
newSubgoal[ data___?OptionQ] := checkProofSuccess[ makePRFSIT[ data]]
newSubgoal[ args___] := unexpected[ newSubgoal, {args}]

checkProofSuccess[ ps_PRFSIT$] := 
	Module[{termRules = getActiveTermRules[ ps]}, 
		Replace[ ps, termRules]
	]
checkProofSuccess[ args___] := unexpected[ checkProofSuccess, {args}]



(* ::Subsection:: *)
(* PRFINFO$ *)

(*
  PRFINFO$[ name_, used_List, generated_List, id_String, addInfo___?OptionQ]
  
	The consturctor understands options name->, used->, generated->, id->, and p."key" (for an
  	arbitrary string "key").
  	The selectors for the datastructure are p.name, p.used, p.generated, p.id, and p."key" (for an
  	arbitrary string "key").
*)

Options[ makePRFINFO] = {name -> "???", used -> {}, generated -> {}, id -> ""};
makePRFINFO[ data___?OptionQ] :=
	Module[{n, u, g, i},
		{n, u, g, i} = {name, used, generated, id} /. {data} /. Options[ makePRFINFO];
		makeRealPRFINFO[ n, u, g, i, Apply[ Sequence, Select[ {data}, isOptComponent]]]
	]
makePRFINFO[ args___] := unexpected[ makePRFINFO, {args}]

makeRealPRFINFO[ name_, u_FML$, g_, id_String, rest___?OptionQ] := makeRealPRFINFO[ name, {u}, g, id, rest]
makeRealPRFINFO[ name_, u_, g_FML$, id_String, rest___?OptionQ] := makeRealPRFINFO[ name, u, {g}, id, rest]
makeRealPRFINFO[ name_, u_List, g_List, "", rest___?OptionQ] := PRFINFO$[ name, u, g, ToString[ Unique[ name]], rest]
makeRealPRFINFO[ name_, u_List, g_List, id_String, rest___?OptionQ] := PRFINFO$[ name, u, g, id, rest]
makeRealPRFINFO[ args___] := unexpected[ makeRealPRFINFO, {args}]

PRFINFO$ /: Dot[ PRFINFO$[ n_, _, _, _, ___], name] := n
PRFINFO$ /: Dot[ PRFINFO$[ _, u_List, _, _, ___], used] := u
PRFINFO$ /: Dot[ PRFINFO$[ _, _, g_List, _, ___], generated] := g
PRFINFO$ /: Dot[ PRFINFO$[ _, _, _, i_String, ___], id] := i
PRFINFO$ /: Dot[ PRFINFO$[ _, _, _, _, ___, (Rule|RuleDelayed)[ key_String, val_], ___], key_] := val
PRFINFO$ /: Dot[ p_PRFINFO$, s___] := unexpected[ Dot, {p, s}]


(* ::Subsection:: *)
(* Local Info datastructure *)

(*
	Local Info datastructure is just a list of Mathematica options, i.e. {key1 -> val1, ..., keyn -> valn}
	Also :> can be used
*)

getLocalInfo[ li_List, key_] :=
	Module[{val = Replace[ key, li]},
		If[ val === key,
			$Failed,
			val
		]
	]
getLocalInfo[ args___] := unexpected[ getLocalInfo, {args}]

putLocalInfo[ li_List, type_[key_, val_]] :=
	Module[{p = Position[ li, (Rule|RuleDelayed)[ key, _]]},
		If[ p === {},
			Append[ li, type[ key, val]],
			ReplacePart[ li, p[[1]] -> type[ key, val]]
		]
	]
putLocalInfo[ args___] := unexpected[ putLocalInfo, {args}]


(* ::Subsection:: *)
(* Proof nodes *)

isProofNode[ obj_] := MatchQ[ obj, _ANDNODE$|_ORNODE$|_TERMINALNODE$]
isProofNode[ args___] := unexpected[ isProofNode, {args}]

proofFails[ pi_PRFINFO$] := TERMINALNODE$[ pi, failed]
proofFails[ args___] := unexpected[ proofFails, {args}]

proofSucceeds[ pi_PRFINFO$] := TERMINALNODE$[ pi, proved]
proofSucceeds[ args___] := unexpected[ proofSucceeds, {args}]

proofDisproved[ pi_PRFINFO$] := TERMINALNODE$[ pi, disproved]
proofDisproved[ args___] := unexpected[ proofDisproved, {args}]

type /: Dot[ node_?isProofNode, type] := Head[ node]
id /: Dot[ node_?isProofNode, id] := First[ node].id
name /: Dot[ node_?isProofNode, name] := First[ node].name
used /: Dot[ node_, used] := Apply[ Union, Map[ #.used&, Cases[ node, _PRFINFO$, Infinity]]]
generated /: Dot[ node_, generated] := Apply[ Union, Map[ #.generated&, Cases[ node, _PRFINFO$, Infinity]]]
proofValue /: Dot[ node_?isProofNode, proofValue] := Last[ node]
proofValue /: Dot[ po_PRFOBJ$, proofValue] := Last[ po]
subgoals /: Dot[ _[ _PRFINFO$, subnodes___, _], subgoals] := {subnodes}

renewID[ node_[ PRFINFO$[ n_, u_, g_, _, rest___?OptionQ], sub___, val_]] := node[ makeRealPRFINFO[ n, u, g, "", rest], sub, val]
renewID[ args___] := unexpected[ renewID, {args}]

makeANDNODE[ pi_PRFINFO$, subnode_] := ANDNODE$[ pi, subnode, pending]
makeANDNODE[ pi_PRFINFO$, {subnodes__}] := ANDNODE$[ pi, subnodes, pending]
makeANDNODE[ args___] := unexpected[ makeANDNODE, {args}]

makeORNODE[ pi_PRFINFO$, {subnodes__}] := ORNODE$[ pi, subnodes, pending]
makeORNODE[ args___] := unexpected[ makeORNODE, {args}]

poToTree[ _TERMINALNODE$|_PRFSIT$] := {}
poToTree[ node_[ pi_PRFINFO$, sub___, val_]] :=
	Module[{root, subTrees, topLevel},
		root = {pi.id, val, node, pi.name};
		subTrees = Flatten[ Map[ poToTree, {sub}]];
		topLevel = Map[ (root -> poNodeToTreeNode[#])&, {sub}];
		Join[ topLevel, subTrees]
	]
poToTree[ args___] := unexpected[ poToTree, {args}]

poNodeToTreeNode[ ps_PRFSIT$] := { ps.id, pending, PRFSIT$, None}
poNodeToTreeNode[ node_[ pi_PRFINFO$, ___, val_]] := { pi.id, val, node, pi.name}
poNodeToTreeNode[ args___] := unexpected[ poNodeToTreeNode, {args}]

propagateProofValues[ poNode:node_[ pi_PRFINFO$, subnodes__, pending]] :=
	Module[ {updSub, subVal, newVal},
		updSub = Map[ propagateProofValues, {subnodes}];
		subVal = Map[ #.proofValue&, updSub];
		newVal = nodeValue[ node, subVal];
		If[ newVal =!= pending,
			$TMAproofTree = With[ {id = pi.id},
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

searchDepthExceeded[ ps_PRFSIT$] := proofFails[ makePRFINFO[ name -> searchDepthLimit, used -> {ps.goal, ps.kb}, id -> ps.id]]
searchDepthExceeded[ args___] := unexpected[ searchDepthExceeded, {args}]

noProofNode[ expr_, i_] := proofFails[ makePRFINFO[ name -> invalidProofNode, used -> {expr}, id -> i]]
noProofNode[ args___] := unexpected[ noProofNode, {args}]


(* ::Subsubsection:: *)
(* getActiveRules *)

(*
	If op =!= Flatten, i.e. we keep a structured list of rules, we need to clarify the role of rulePriority, maybe sort sublists recursively? *)
getActiveRules[ ps_PRFSIT$, op_:Identity] := 
	Module[{rules, act, prio, names},
		(* Select names of active rules, delete termination rules, strings (category names) and inactive rules, finally apply op *)
		{rules, act, prio} = ps.ruleSetup;
		names = op[ rules /. {{r_, _, _, _Integer, "term"} -> Sequence[],
			{r_ /; Replace[ r, act], _, _, _Integer, ___} -> r, _String | {r_Symbol, _, _, _Integer, ___} -> Sequence[]}];
		If[ Depth[ names] == 2,
			(* we have a flat list of rule names *)
			names = Sort[ DeleteDuplicates[ names], Replace[ #1, prio] < Replace[ #2, prio] &];
			DeleteCases[ Map[ inferenceRule, names], _inferenceRule],
			(* else *)
			DeleteCases[ MapAt[ inferenceRule, names, Position[ names, _Symbol, Heads -> False]], _inferenceRule, Infinity]
		]
	]	
getActiveRules[ args___] := unexpected[ getActiveRules, {args}]

getActiveTermRules[ ps_PRFSIT$] :=
	Module[{rules, act, prio, names},
		(* Select names of active rules, delete strings (category names) and inactive rules, finally apply op *)
		{rules, act, prio} = ps.ruleSetup;
		names = Cases[ rules, {r_ /; Replace[ r, act], _, _, _Integer, "term"} -> r, Infinity];
		Assert[ MatchQ[ names, {__Symbol}]];
		(* we have a flat list of rule names *)
		names = Sort[ DeleteDuplicates[ names], Replace[ #1, prio] < Replace[ #2, prio] &];
		DeleteCases[ Map[ inferenceRule, names], _inferenceRule]
	]
getActiveTermRules[ args___] := unexpected[ getActiveTermRules, {args}]


(* ::Subsubsection:: *)
(* applyAllRules *)

applyAllRules[ ps_PRFSIT$, rules_List] :=
	DeleteCases[ ReplaceList[ ps, rules], $Failed]
applyAllRules[ args___] := unexpected[ applyAllRules, {args}]


(* ::Subsubsection:: *)
(* showProofNavigation *)

showProofNavigation[ {}, scale_] := Graphics[ {}, ImageSize -> {350,420}]

(*
The initial proof tree already has an edge from original PS to initial PS, so this should not be called anymore

showProofNavigation[ {Depth -> _, node_List}, scale_] := Graphics[ proofStepNode[ {0, 0}, node, 18], ImageSize -> {350,420}, PlotRegion -> {{0.4, 0.6}, {0.6, 0.8}}]
*)

showProofNavigation[ {p__Rule}, scale_] :=
    Module[ {root = Cases[ {p}, {"OriginalPS", __}, {2}], geometry, font},
    	If[ scale === Fit,
    		geometry = {350,420},
    		(* else *)
    		geometry = {Max[ Count[ {p}, _ -> {__, TERMINALNODE$|PRFSIT$, _}]*20, 350], Max[ $TMAcurrentDepth*15, 420]}*scale
    	];
    	font = 18-Ceiling[ Apply[ Times, geometry]/(350*420)];
        If[ root === {},
            translate[ "noRoot"],
            TreePlot[ {p}, Automatic, First[ root], VertexRenderingFunction -> (proofStepNode[ #1, #2, font]&),
            EdgeRenderingFunction -> ({Dashed, GrayLevel[0.5], Line[#1]}&), ImageSize -> geometry, AspectRatio -> 1/Apply[ Divide, geometry]]
        ]
    ]
showProofNavigation[ args___] := unexpected[ showProofNavigation, {args}]

proofStepNode[ pos_List, node:{ id_String, status_, type_, name_}, font_] := 
	Module[{opacity = If[ TrueQ[ ruleTextActive[ name]], 1, 0.3]},
		{
		Switch[ status,
			pending, RGBColor[0.360784, 0.67451, 0.933333, opacity] (* steelblue *),
			failed, RGBColor[1, 0.270588, 0, opacity] (* orangered *),
			proved, RGBColor[0, 0.780392, 0.54902, opacity] (* turquoiseblue *),
			_, Black],
		Switch[ type,
			PRFSIT$|PRFOBJ$, Disk[ pos, 0.1],
			TERMINALNODE$, Map[ (pos + 0.1*#)&, Rectangle[ {-Sqrt[Pi]/2, -Sqrt[Pi]/2}, {Sqrt[Pi]/2, Sqrt[Pi]/2}]],
			ANDNODE$, Polygon[ Map[ (pos + 0.125*#)&, {{0,1}, {Cos[7*Pi/6], Sin[7*Pi/6]}, {Cos[11*Pi/6], Sin[11*Pi/6]}}]],
			ORNODE$, Polygon[ Map[ (pos + 0.125*#)&, {{0,-1}, {Cos[Pi/6], Sin[Pi/6]}, {Cos[5*Pi/6], Sin[5*Pi/6]}}]],
			_, Map[ (pos + 0.1*#)&, Rectangle[ {-Sqrt[Pi]/2, -Sqrt[Pi]/2}, {Sqrt[Pi]/2, Sqrt[Pi]/2}]]],
		{Black, Dynamic[ Text[ 
			Hyperlink[
				Switch[ type, 
        				TERMINALNODE$, proofStatusIndicator[ status, name],
         				PRFOBJ$, proofStatusIndicator[ status],
       				_, proofNodeIndicator[ status, type, name]], 
				{CurrentValue[ $TMAproofNotebook, "NotebookFileName"], id},
				BaseStyle -> {FontSize -> font}, Active -> ruleTextActive[ name]], pos]]}
		}
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
	proofStatusIndicator[ status],
	translate[ SymbolName[ status]] <> If[ status =!= pending, " (" <> MessageName[ name, "usage"] <> ")", ""]]
	
proofStatusIndicator[ args___] := unexpected[ proofStatusIndicator, {args}]

proofNodeIndicator[ status_, type_, name_] :=
	Module[ {label, description},
		{label, description} = Switch[ type,
			PRFSIT$, {"?", translate[ "open proof situation"]},
        	ANDNODE$, {"\[Wedge]", MessageName[ name, "usage"]},
        	ORNODE$, {"\[Vee]", MessageName[ name, "usage"]},
        	_, {"\[DownQuestion]", translate[ "unknown proof node"]}
		];
		Tooltip[ Style[ label, ShowStringCharacters -> False], description <> " (" <> translate[ SymbolName[ status]] <> ")"]
	]
proofNodeIndicator[ args___] := unexpected[ proofNodeIndicator, {args}]

(* ::Subsubsection:: *)
(* makeInitialProofObject *)

(*
	localInfo remains {} in the initial proof object
*)
makeInitialProofObject[ g_FML$, k_List, {r_Hold, act_List, prio_List}, s_] :=
    Module[ {dummyPO},
        dummyPO = PRFOBJ$[
            makePRFINFO[ name -> initialProofSituation, used -> {g, k}, id -> "OriginalPS"],
            PRFSIT$[ g, k, "InitialPS"],
            pending
        ];
        (* Use propagateProofValues and replaceProofSit in order to update the proof tree correspondingly *)
        propagateProofValues[ 
            replaceProofSit[ dummyPO,
            	{2} -> newSubgoal[ goal -> g, kb -> k, id -> "InitialPS",
                	rules -> r, ruleActivity -> act, rulePriority -> prio, strategy -> s]]
        ]
    ]
makeInitialProofObject[ args___] := unexpected[ makeInitialProofObject, {args}]


(* ::Subsubsection:: *)
(* makeInitialProofNotebook *)

makeInitialProofNotebook[ p_PRFOBJ$] :=
    Module[ { cells, t, nb},
        cells = proofObjectToCell[ p];
        $proofInProgressMarker = With[ {v1 = RandomReal[{1,5}], v2 = RandomReal[{1,5}]}, 
        	{Cell[BoxData[
        				DynamicBox[ ToBoxes[ Graphics[{Circle[{0, 0}, 1],
        					Table[Text[ToString[t], 0.8*{Cos[Pi/2 - (Pi/6)*t], Sin[Pi/2 - (Pi/6)*t]}, BaseStyle -> {FontSize -> 5}], {t, 1, 12}],
        					{Hue[ Clock[], 1, Clock[]], Opacity[0.5], Disk[{0, 0}, 1, {Pi/2 - 2/v1*Pi*Clock[v1], Pi/4 - 2/v1*Pi*Clock[v1]}]},
        					{Hue[ Clock[], 1, Clock[]], Opacity[0.5], Disk[{0, 0}, 1, {Pi/2 + 2/v2*Pi*Clock[v2], Pi/4 + 2/v2*Pi*Clock[v2]}]},
        					{White, Disk[{0, 0}, 0.7]}}, ImageSize -> {50, 50}], 
        					StandardForm], ImageSizeCache -> {50., {23., 27.}}]],
        				"Output", TextAlignment -> Center]}];
        nb = NotebookPut[
            	Notebook[ cells, Visible -> False, StyleDefinitions -> makeColoredStylesheet[ "Proof"]]];
        nb
    ]
makeInitialProofNotebook[ args___] := unexpected[ makeInitialProofNotebook, {args}]


(* ::Subsubsection:: *)
(* makeInitialProofTree *)

makeInitialProofTree[ ] := {{"OriginalPS", pending, PRFOBJ$, None} -> {"InitialPS", pending, PRFSIT$, None}}
makeInitialProofTree[ args___] := unexpected[ makeInitialProofTree, {args}]

(* ::Subsubsection:: *)
(* displayProof *)

displayProof[ p_PRFOBJ$] :=
	Module[{ cells},
		cells = proofObjectToCell[ p];
		NotebookClose[ $TMAproofNotebook];
		$TMAproofNotebook = NotebookPut[ Notebook[ cells, StyleDefinitions -> makeColoredStylesheet[ "Proof"]]]
	]
displayProof[ args___] := unexpected[ displayProof, {args}]


(* ::Subsubsection:: *)
(* proofObjectToCell *)

(* 
	If proof text is deactivated, the result is {}. Proof texts are composed in such a way that {} simply cancels out and therfore no text appears.
*)
proofObjectToCell[ PRFOBJ$[ pi_PRFINFO$, sub_, pVal_]] := 
	Module[{ cellList = proofObjectToCell[ pi, pVal]},
		Join[ cellList, {proofObjectToCell[ sub]}]
	]
proofObjectToCell[ PRFINFO$[ name_?ruleTextActive, u_, g_, id_String, rest___?OptionQ], pVal_] := proofStepTextId[ id, name, u, g, rest, pVal]
proofObjectToCell[ PRFINFO$[ _, _, _, _String, ___?OptionQ], _] := {}
proofObjectToCell[ PRFSIT$[ g_FML$, kb_List, id_String, ___]] := Cell[ CellGroupData[ proofStepTextId[ id, openProofSituation, {g, kb}, {}], $proofCellStatus]]
proofObjectToCell[ (ANDNODE$|ORNODE$)[ pi_PRFINFO$, subnodes__, pVal_]] := 
	Module[{header, sub = {}},
		header = proofObjectToCell[ pi, pVal];
		If[ Length[ {subnodes}] == 1,
			sub = {proofObjectToCell[ subnodes]},
			(* else *)
			sub = MapIndexed[ subProofToCell[ pi, #1, #2]&, {subnodes}]
		];
		If[ header === {},
			Apply[ Sequence, sub],
			(* else *)
			Cell[ CellGroupData[ Join[ header, sub], $proofCellStatus]]
		]
	]
proofObjectToCell[ TERMINALNODE$[ pi_PRFINFO$, pVal_]] := 
	Cell[ CellGroupData[ proofObjectToCell[ pi, pVal], $proofCellStatus]]
	
proofObjectToCell[ args___] := unexpected[ proofObjectToCell, {args}]

subProofToCell[ PRFINFO$[ name_, used_List, gen_List, ___], node_, pos_List] :=
	Cell[ CellGroupData[ Join[ subProofHeaderId[ node.id, name, used, gen, node.proofValue, pos], {proofObjectToCell[ node]}], $proofCellStatus]]
subProofToCell[ args___] := unexpected[ subProofToCell, {args}]


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