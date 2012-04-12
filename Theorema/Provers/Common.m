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
		Clear[ ruleAct];
		ruleAct[_] := True;
		$proofCellStatus = Open;
	]

callProver[ rules_, strategy_, goal_, kb_, searchDepth_] :=
	Module[{},
		$TMAproofObject = makeInitialProofObject[ goal, kb, rules, strategy];
		$TMAproofNotebook = makeInitialProofNotebook[ $TMAproofObject];
		$TMAproofTree = makeInitialProofTree[];
		initFormulaLabel[];
		proofSearch[ searchDepth];
  		$proofInProgressMarker = {};
  		If[ $TMAproofTree === {},
  			$TMAproofTree = {poNodeToTreeNode[ $TMAproofObject]}
  		];
		{getProofValue[ $TMAproofObject], $TMAproofObject}
	]
callProver[ args___] := unexpected[ callProver, {args}]


(* ::Subsubsection:: *)
(* proofSearch *)

proofSearch[ searchDepth_Integer] :=
    Module[ {openPSpos, openPS, selPSpos, selPS, pStrat, newSteps},
    	$proofAborted = False;
        While[ !$proofAborted && getProofValue[] === pending && (openPSpos = Position[ $TMAproofObject, _PRFSIT$]) =!= {},
            openPS = Extract[ $TMAproofObject, openPSpos];
            {selPS, selPSpos} = chooseNextPS[ openPS, openPSpos];
            If[ Length[ selPSpos] > searchDepth,
            	newSteps = searchDepthExceeded[ selPS],
            	(* else *)
            	pStrat = getStrategy[ selPS];
            	newSteps = pStrat[ getRules[ selPS], selPS]
            ];
            If[ !isProofNode[ newSteps],
            	newSteps = noProofNode[ newSteps, getNodeID[ selPS]];
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
        While[ !$proofAborted && getProofValue[] === pending && (openPSpos = Position[ $TMAproofObject, _PRFSIT$]) =!= {},
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
            pStrat = getStrategy[ selPS];
            newSteps = pStrat[ getRules[ selPS], selPS]
        ];
        If[ !isProofNode[ newSteps],
            newSteps = noProofNode[ newSteps, getNodeID[ selPS]];
        ];
        $TMAproofObject = replaceProofSit[ $TMAproofObject, selPSpos -> newSteps];
        $TMAproofObject = propagateProofValues[ $TMAproofObject]
    ]
proofSearchAtPos[ args___] := unexpected[ proofSearchAtPos, {args}]

chooseNextPS[ ps_List, psPos_List] :=
	Module[{},
		{First[ ps], First[ psPos]}
	]
chooseNextPS[ args___] := unexpected[ chooseNextPS, {args}]

replaceProofSit[ po_PRFOBJ$, pos_ -> new:node_[___]] :=
	Module[{parentID = getNodeID[ Extract[ po, pos]], newVal = getProofValue[ new], sub},
		sub = poToTree[ new];
		$TMAproofTree = Join[ $TMAproofTree /. {parentID, pending, PRFSIT$} -> {parentID, newVal, node}, sub];
		ReplacePart[ po, pos -> new]
	]
replaceProofSit[ args___] := unexpected[ replaceProofSit, {args}]


(* ::Section:: *)
(* Proof object data structures *)

getGoal[ PRFSIT$[ g_, kb_, af_, ___]] := g
getGoal[ args___] := unexpected[ getGoal, {args}]

getKB[ PRFSIT$[ g_, kb_, af_, ___]] := kb
getKB[ args___] := unexpected[ getKB, {args}]

getRules[ PRFSIT$[ g_, kb_, af_, ___, "InferenceRules" -> r_, ___]] := r
getRules[ args___] := unexpected[ getRules, {args}]

getStrategy[ PRFSIT$[ g_, kb_, af_, ___, "Strategy" -> s_, ___]] := s
getStrategy[ args___] := unexpected[ getStrategy, {args}]

getPrincipalData[ PRFSIT$[ g_, kb_, af_, ___]] := {g, kb, af}
getPrincipalData[ args___] := unexpected[ getPrincipalData, {args}]

getProofValue[ ] := Last[ $TMAproofObject]
getProofValue[ _PRFSIT$] := pending
getProofValue[ node_] := Last[ node]
getProofValue[ args___] := unexpected[ getProofValue, {args}]

getNodeID[ PRFINFO$[ ___, id_String]] := id
getNodeID[ PRFSIT$[ _FML$, _List, _, id_String, ___Rule]] := id
getNodeID[ node_?isProofNode] := getNodeID[ First[ node]]
getNodeID[ args___] := unexpected[ getNodeID, {args}]

getUsed[ PRFINFO$[ _, used_List, _, ___]] := used
getUsed[ node_] := Apply[ Union, Map[ getUsed, Cases[ node, _PRFINFO$, Infinity]]]
getUsed[ args___] := unexpected[ getUsed, {args}]

getGenerated[ PRFINFO$[ _, _, generated_List, ___]] := generated
getGenerated[ node_] := Apply[ Union, Map[ getGenerated, Cases[ node, _PRFINFO$, Infinity]]]
getGenerated[ args___] := unexpected[ getGenerated, {args}]

getActiveRules[ Hold[ rules_], op_:Identity] := DeleteDuplicates[ DeleteCases[ op[ rules], _String|_?(ruleAct[#]===False&), Infinity]]
getActiveRules[ args___] := unexpected[ getActiveRules, {args}]

isProofNode[ obj_] := MatchQ[ obj, _ANDNODE$|_ORNODE$|_TERMINALNODE$]
isProofNode[ args___] := unexpected[ isProofNode, {args}]

Options[ makePRFINFO] = {name -> "???", used -> {}, generated -> {}, id -> ""};
makePRFINFO[ data___?OptionQ] :=
	Module[{n, u, g, i},
		{n, u, g, i} = {name, used, generated, id} /. {data} /. Options[ makePRFINFO];
		makeRealPRFINFO[ n, u, g, i]
	]
makePRFINFO[ args___] := unexpected[ makePRFINFO, {args}]

makeRealPRFINFO[ name_, u_FML$, g_, id_String] := makeRealPRFINFO[ name, {u}, g, id]
makeRealPRFINFO[ name_, u_, g_FML$, id_String] := makeRealPRFINFO[ name, u, {g}, id]
makeRealPRFINFO[ name_, u_List, g_List, ""] := PRFINFO$[ name, u, g, ToString[ Unique[ name]]]
makeRealPRFINFO[ name_, u_List, g_List, id_String] := PRFINFO$[ name, u, g, id]
makeRealPRFINFO[ args___] := unexpected[ makeRealPRFINFO, {args}]

Options[ makePRFSIT] = {goal -> {}, kb -> {}, facts -> {}, id :> ToString[ Unique[ "PRFSIT$"]]};
makePRFSIT[ data___?OptionQ] :=
	Module[{g, k, f, i},
		{g, k, f, i} = {goal, kb, facts, id} /. {data} /. Options[ makePRFSIT];
		makeRealPRFSIT[ g, k, f, i, Apply[ Sequence, Cases[ {data}, HoldPattern[ _String -> _]]]]
	]
makePRFSIT[ args___] := unexpected[ makePRFINFO, {args}]

makeRealPRFSIT[ g_FML$, k_List, af_, id_String, rest___Rule] := 
	Module[ {succ, pi},
		{succ, pi} = checkProofSuccess[ g, k, af, id];
		If[ succ,
			proofSucceeds[ pi],
			PRFSIT$[ g, k, af, id, rest]
		]
	]
makeRealPRFSIT[ args___] := unexpected[ makeRealPRFSIT, {args}]

renewID[ node_[ PRFINFO$[ n_, u_, g_, _], sub___, val_]] := node[ makeRealPRFINFO[ n, u, g, ""], sub, val]
renewID[ args___] := unexpected[ renewID, {args}]

checkProofSuccess[ goal_FML$, {___, k:FML$[ _, phi_, _], ___, c:FML$[ _, Not$TM[ phi_], _], ___}, af_, i_String] := 
	{True, makePRFINFO[ name -> contradictionKB, used -> {k, c}, id -> i]}
checkProofSuccess[ goal_FML$, {___, k:FML$[ _, Not$TM[ phi_], _], ___, c:FML$[ _, phi_, _], ___}, af_, i_String] := 
	{True, makePRFINFO[ name -> contradictionKB, used -> {k, c}, id -> i]}
checkProofSuccess[ goal_FML$, {___, k:FML$[ _, False, _], ___}, af_, i_String] := 
	{True, makePRFINFO[ name -> falseInKB, used -> k, id -> i]}
checkProofSuccess[ goal:FML$[ _, g_, _], {___, k:FML$[ _, g_, _], ___}, af_, i_String] := 
	{True, makePRFINFO[ name -> goalInKB, used -> {goal, k}, id -> i]}
checkProofSuccess[ goal_FML$, kb_, af_, id_String] := {False, PRFINFO$[]}
checkProofSuccess[ args___] := unexpected[ checkProofSuccess, {args}]

proveAll[ pi_PRFINFO$, subnodes__] := ANDNODE$[ pi, subnodes, pending]
proveAll[ args___] := unexpected[ proveAll, {args}]

proveSome[ pi_PRFINFO$, subnodes__] := ORNODE$[ pi, subnodes, pending]
proveSome[ args___] := unexpected[ proveSome, {args}]

getSubgoals[ _[ _PRFINFO$, subnodes___, _]] := {subnodes}
getSubgoals[ args___] := unexpected[ getSubgoals, {args}]

poToTree[ _TERMINALNODE$|_PRFSIT$] := {}
poToTree[ node_[ pi_PRFINFO$, sub___, val_]] :=
	Module[{root, subTrees, topLevel},
		root = { getNodeID[ pi], val, node};
		subTrees = Flatten[ Map[ poToTree, {sub}]];
		topLevel = Map[ (root -> poNodeToTreeNode[#])&, {sub}];
		Join[ topLevel, subTrees]
	]
poToTree[ args___] := unexpected[ poToTree, {args}]

poNodeToTreeNode[ ps_PRFSIT$] := { getNodeID[ ps], pending, PRFSIT$}
poNodeToTreeNode[ node_[ pi_PRFINFO$, ___, val_]] := { getNodeID[ pi], val, node}
poNodeToTreeNode[ args___] := unexpected[ poNodeToTreeNode, {args}]

propagateProofValues[ poNode:node_[ pi_PRFINFO$, subnodes__, pending]] :=
	Module[ {updSub, subVal, newVal},
		updSub = Map[ propagateProofValues, {subnodes}];
		subVal = Map[ getProofValue, updSub];
		newVal = nodeValue[ node, subVal];
		If[ newVal =!= pending,
			$TMAproofTree = With[ {id = getNodeID[ pi]},
				$TMAproofTree /. {id, pending, t_} -> {id, newVal, t}
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

searchDepthExceeded[ ps_PRFSIT$] := proofFails[ makePRFINFO[ name -> searchDepthLimit, used -> {getGoal[ ps], getKB[ ps]}, id -> getNodeID[ ps]]]
searchDepthExceeded[ args___] := unexpected[ searchDepthExceeded, {args}]

noProofNode[ expr_, i_] := proofFails[ makePRFINFO[ name -> invalidProofNode, used -> {expr}, id -> i]]
noProofNode[ args___] := unexpected[ noProofNode, {args}]

proofFails[ pi_PRFINFO$] := TERMINALNODE$[ pi, failed]
proofFails[ args___] := unexpected[ proofFails, {args}]

proofSucceeds[ pi_PRFINFO$] := TERMINALNODE$[ pi, proved]
proofSucceeds[ args___] := unexpected[ proofSucceeds, {args}]

proofDisproved[ pi_PRFINFO$] := TERMINALNODE$[ pi, disproved]
proofDisproved[ args___] := unexpected[ proofDisproved, {args}]

(* ::Subsubsection:: *)
(* showProofNavigation *)

showProofNavigation[ {}, geometry_List] := ""
showProofNavigation[ {node_List}, geometry_List] := Graphics[ proofStepNode[ {0, 0}, node, 18], ImageSize -> geometry, PlotRegion -> {{0.4, 0.6}, {0.6, 0.8}}]

showProofNavigation[ p:{__Rule}, geometry_List] :=
    Module[ {root = Cases[ p, {"InitPS", __}, {2}], font = 18-Ceiling[ Apply[ Times, geometry]/(350*450)]},
        If[ root === {},
            translate[ "noRoot"],
            TreePlot[ p, Automatic, First[ root], VertexRenderingFunction -> (proofStepNode[ #1, #2, font]&),
            EdgeRenderingFunction -> ({Dashed, GrayLevel[0.5], Line[#1]}&), ImageSize -> geometry, AspectRatio -> 1/Apply[ Divide, geometry]]
        ]
    ]
showProofNavigation[ args___] := unexpected[ showProofNavigation, {args}]

proofStepNode[ pos_List, node:{ id_String, status_, type_}, font_] := 
	{
		Switch[ status,
			pending, RGBColor[0.360784, 0.67451, 0.933333] (* steelblue *),
			failed, RGBColor[1, 0.270588, 0] (* orangered *),
			proved, RGBColor[0, 0.780392, 0.54902] (* turquoiseblue *),
			_, Black],
		Switch[ type,
			PRFSIT$, Disk[ pos, 0.1],
			TERMINALNODE$|PRFOBJ$, Map[ (pos + 0.1*#)&, Rectangle[ {-Sqrt[Pi]/2, -Sqrt[Pi]/2}, {Sqrt[Pi]/2, Sqrt[Pi]/2}]],
			_, Polygon[ Map[ (pos + 0.125*#)&, {{0,1}, {Cos[7*Pi/6], Sin[7*Pi/6]}, {Cos[11*Pi/6], Sin[11*Pi/6]}}]]],
		{Black, Dynamic[ Text[ 
			Hyperlink[
				Switch[ type, 
        				TERMINALNODE$|PRFOBJ$, proofStatusIndicator[ status],
        				_, proofNodeIndicator[ status, type]], 
				{CurrentValue[ $TMAproofNotebook, "NotebookFileName"], id},
				BaseStyle -> {FontSize -> font}], pos]]}
	}
proofStepNode[ args___] := unexpected[ proofStepNode, {args}]

proofStatusIndicator[ status_] :=
	Module[ {label},
		label = Switch[ status, 
			proved, "\[CheckmarkedBox]",
			disproved, "\[Times]",
			failed, "\[WarningSign]",
			pending, "?",
			_, "\[DownQuestion]"
		];
		Tooltip[ Style[ label, ShowStringCharacters -> False], translate[ SymbolName[ status]]]
	]
proofStatusIndicator[ args___] := unexpected[ proofStatusIndicator, {args}]

proofNodeIndicator[ status_, type_] :=
	Module[ {label, description},
		{label, description} = Switch[ type,
			PRFSIT$, {"?", "open proof situation"},
        	ANDNODE$, {"\[Wedge]", "conjunction of subproofs"},
        	ORNODE$, {"\[Vee]", "disjunction of subproofs"},
        	_, {"\[DownQuestion]", "unknown proof node"}
		];
		Tooltip[ Style[ label, ShowStringCharacters -> False], translate[ description] <> ": " <> translate[ SymbolName[ status]]]
	]
proofNodeIndicator[ args___] := unexpected[ proofNodeIndicator, {args}]

(* ::Subsubsection:: *)
(* makeInitialProofObject *)

makeInitialProofObject[ g_FML$, k_List, rules_Hold, strategy_] :=
	PRFOBJ$[
		makePRFINFO[ name -> initialProofSituation, used -> {g, k}, id -> "InitPS"],
		makePRFSIT[ goal -> g, kb -> k, id -> "InitPS", "InferenceRules" -> rules, "Strategy" -> strategy],(*additional facts {}*)
		pending
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
            	Notebook[ cells, Visible -> False, StyleDefinitions -> FileNameJoin[{"Theorema", "Proof.nb"}]]];
        nb
    ]
makeInitialProofNotebook[ args___] := unexpected[ makeInitialProofNotebook, {args}]


(* ::Subsubsection:: *)
(* makeInitialProofTree *)

makeInitialProofTree[ ] := {}
makeInitialProofTree[ args___] := unexpected[ makeInitialProofTree, {args}]

(* ::Subsubsection:: *)
(* displayProof *)

displayProof[ p_PRFOBJ$] :=
	Module[{ cells},
		cells = proofObjectToCell[ p];
		NotebookClose[ $TMAproofNotebook];
		$TMAproofNotebook = NotebookPut[ Notebook[ cells, StyleDefinitions -> FileNameJoin[{"Theorema", "Proof.nb"}]]]
	]
displayProof[ args___] := unexpected[ displayProof, {args}]


(* ::Subsubsection:: *)
(* proofObjectToCell *)

proofObjectToCell[ PRFOBJ$[ pi_PRFINFO$, sub_, pVal_]] := 
	Module[{ cellList = proofObjectToCell[ pi, pVal]},
		Append[ cellList, proofObjectToCell[ sub]]
	]
proofObjectToCell[ PRFINFO$[ name_, rest___, i_String], pVal_] := proofStepText[ id -> i, name, $Language, rest, pVal]
proofObjectToCell[ PRFSIT$[ g_FML$, kb_List, _, i_String, ___]] := Cell[ CellGroupData[ proofStepText[ id -> i, openProofSituation, $Language, {g, kb}, {}], $proofCellStatus]]
proofObjectToCell[ (ANDNODE$|ORNODE$)[ pi_PRFINFO$, subnodes__, pVal_]] := 
	Module[{header, sub = {}},
		header = proofObjectToCell[ pi, pVal];
		If[ Length[ {subnodes}] == 1,
			sub = {proofObjectToCell[ subnodes]},
			(* else *)
			sub = MapIndexed[ subProofToCell[ pi, #1, #2]&, {subnodes}]
		];
		Cell[ CellGroupData[ Join[ header, sub], $proofCellStatus]]
	]
proofObjectToCell[ TERMINALNODE$[ pi_PRFINFO$, pVal_]] := 
	Cell[ CellGroupData[ proofObjectToCell[ pi, pVal], $proofCellStatus]]
	
proofObjectToCell[ args___] := unexpected[ proofObjectToCell, {args}]

subProofToCell[ PRFINFO$[ name_, used_List, gen_List, ___], node_, pos_List] :=
	Cell[ CellGroupData[ Append[ subProofHeader[ id -> getNodeID[ node], name, $Language, used, gen, getProofValue[ node], pos], proofObjectToCell[ node]], $proofCellStatus]]
subProofToCell[ args___] := unexpected[ subProofToCell, {args}]


(* ::Section:: *)
(* register provers *)

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