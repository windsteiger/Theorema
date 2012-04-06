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

getNodeID[ (PRFSIT$|PRFINFO$)[ ___, "ID" -> id_, ___]] := id
getNodeID[ node_?isProofNode] := getNodeID[ First[ node]]
getNodeID[ args___] := unexpected[ getNodeID, {args}]

getUsed[ PRFINFO$[ _, used_List, _, ___]] := used
getUsed[ args___] := unexpected[ getUsed, {args}]

getGenerated[ PRFINFO$[ _, _, generated_List, ___]] := generated
getGenerated[ args___] := unexpected[ getGenerated, {args}]

getActiveRules[ Hold[ rules_], op_:Identity] := DeleteDuplicates[ DeleteCases[ op[ rules], _String|_?(ruleAct[#]===False&), Infinity]]
getActiveRules[ args___] := unexpected[ getActiveRules, {args}]

isProofNode[ obj_] := MatchQ[ obj, _ANDNODE$|_ORNODE$|_TERMINALNODE$]
isProofNode[ args___] := unexpected[ isProofNode, {args}]

makePRFINFO[ name_String, g_, k_] := PRFINFO$[ name, g, k, "ID" -> ToString[ Unique[ name]]]
makePRFINFO[ name_String, g_, k_, id_String] := PRFINFO$[ name, g, k, "ID" -> id]
makePRFINFO[ args___] := unexpected[ makePRFINFO, {args}]

makePRFSIT[ g_, k_, af_, rest___Rule] := PRFSIT$[ g, k, af, rest, "ID" -> ToString[ Unique[ "PRFSIT$"]]]
makePRFSIT[ g_, k_, af_, id_String, rest___Rule] := PRFSIT$[ g, k, af, rest, "ID" -> id]
makePRFSIT[ args___] := unexpected[ makePRFSIT, {args}]

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

searchDepthExceeded[ ps_PRFSIT$] := proofFails[ makePRFINFO[ "SearchDepth", getGoal[ ps], getKB[ ps], getNodeID[ ps]]]
searchDepthExceeded[ args___] := unexpected[ searchDepthExceeded, {args}]

noProofNode[ expr_, id_] := proofFails[ makePRFINFO[ "NoPNode", expr, {}, id]]
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
    Module[ {root = Cases[ p, {"Initial", __}, {2}], font = 18-Ceiling[ Apply[ Times, geometry]/(350*450)]},
        If[ root === {},
            translate[ "noRoot"],
            TreePlot[ p, Automatic, First[ root], VertexRenderingFunction -> (proofStepNode[ #1, #2, font]&),
            EdgeRenderingFunction -> ({Dashed, GrayLevel[0.5], Line[#1]}&), ImageSize -> geometry, AspectRatio -> 1/Apply[ Divide, geometry]]
        ]
    ]
showProofNavigation[ args___] := unexpected[ showProofNavigation, {args}]

proofStepNode[ pos_List, node:{ id_, status_, type_}, font_] := 
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
       					PRFSIT$, "?",
        				ANDNODE$, "\[Wedge]",
        				ORNODE$, "\[Vee]",
        				TERMINALNODE$|PRFOBJ$, Switch[ status, proved, "\[CheckmarkedBox]", disproved, "\[Times]", failed, "\[WarningSign]", _, "\[DownQuestion]"]], 
				{CurrentValue[ $TMAproofNotebook, "NotebookFileName"], id},
				BaseStyle -> {FontSize -> font}], pos]]}
	}
proofStepNode[ args___] := unexpected[ proofStepNode, {args}]

(* ::Subsubsection:: *)
(* makeInitialProofObject *)

makeInitialProofObject[ goal_, kb_, rules_, strategy_] :=
	PRFOBJ$[
		makePRFINFO[ "Initial", goal, kb, "Initial"],
		makePRFSIT[ goal, kb, {}(*additional facts*), "Initial", "InferenceRules" -> rules, "Strategy" -> strategy],
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
proofObjectToCell[ PRFINFO$[ name_String, rest___, "ID" -> id_], pVal_] := proofStepText[ "ID" -> id, name, $Language, rest, pVal]
proofObjectToCell[ PRFSIT$[ g_, kb_, ___, "ID" -> id_]] := Cell[ CellGroupData[ proofStepText[ "ID" -> id, "ProofSituation", $Language, g, kb], $proofCellStatus]]
proofObjectToCell[ (ANDNODE$|ORNODE$)[ pi_PRFINFO$, subnodes__, pVal_]] := 
	Module[{header, sub},
		header = proofObjectToCell[ pi, pVal];
		(*sub = Map[ proofObjectToCell, {subnodes}];*)
		sub = MapIndexed[ subProofToCell[ pi, #1, #2]&, {subnodes}];
		Cell[ CellGroupData[ Join[ header, sub], $proofCellStatus]]
	]
proofObjectToCell[ TERMINALNODE$[ pi_PRFINFO$, pVal_]] := 
	Cell[ CellGroupData[ proofObjectToCell[ pi, pVal], $proofCellStatus]]
	
proofObjectToCell[ args___] := unexpected[ proofObjectToCell, {args}]

subProofToCell[ PRFINFO$[ name_, used_, gen_, ___], node_, pos_List] :=
		Cell[ CellGroupData[ Append[ subProofHeader[ "ID" -> getNodeID[ node], name, $Language, used, gen, pos], proofObjectToCell[ node]], $proofCellStatus]]
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