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
		ruleAct[_] := True;
	]

callProver[ rules_, strategy_, goal_, kb_] :=
	Module[{},
		$TMAproofObject = makeInitialProofObject[ goal, kb, rules, strategy];
		$TMAproofNotebook = makeInitialProofNotebook[ $TMAproofObject];
		$TMAproofTree = makeInitialProofTree[ ];
		proofSearch[ ];
		Pause[1];
		$TMAproofTree = {{"Initial", "pending", "andNode"} -> {"new1", "pending", "prfsit"},
  			{"Initial", "pending", "andNode"} -> {"new2", "pending", "prfsit"}};
  		Pause[2];
  		$TMAproofTree = $TMAproofTree /. {"new2", _, _} -> {"new2", "pending", "andNode"};
  		AppendTo[ $TMAproofTree, {"new2", "pending", "andNode"} -> {"new3", "proved", "terminalNode"}];
  		Pause[2];
  		$TMAproofTree = $TMAproofTree /. {id_, "pending", "andNode"} -> {id, "proved", "andNode"};
  		Pause[4];
  		$proofInProgressMarker = {};
		{$Failed, $TMAproofObject}
	]
callProver[ args___] := unexpected[ callProver, {args}]


(* ::Subsubsection:: *)
(* proofSearch *)

proofSearch[ ] :=
	Module[{openPS, openPSpos, selPSpos, selPS},
		openPSpos = Position[ $TMAproofObject, PRFSIT$[ _, _, _, "pending", ___]];
		openPS = Extract[ $TMAproofObject, openPSpos];
		selPSpos = chooseNextPS[ openPS, openPSpos];
	]
proofSearch[ args___] := unexpected[ proofSearch, {args}]

(* ::Subsubsection:: *)
(* showProofNavigation *)

showProofNavigation[ {node:{id_, status_, type_}}] := Graphics[ makeNode[ node, {0, 0}], ImageSize -> {350, 450}, PlotRegion -> {{0.45, 0.55}, {0.9, 1}}]

showProofNavigation[ p:{__Rule}] := TreePlot[ p, VertexRenderingFunction -> proofStepNode,
	EdgeRenderingFunction -> ({Dashed, GrayLevel[0.5], Line[#1]}&), ImageSize -> Max[{1, Length[p]/100}]*{350, 450}, AspectRatio -> Automatic]
showProofNavigation[ p_] := ""
showProofNavigation[ args___] := unexpected[ showProofNavigation, {args}]

proofStepNode[ pos_, node:{_, _, _}, ___] := makeNode[ node, pos]
proofStepNode[ args___] := unexpected[ proofStepNode, {args}]

makeNode[ node:{ id_, status_, type_}, pos_List] := 
	{
		Switch[ status,
			"pending", RGBColor[0.360784, 0.67451, 0.933333] (* steelblue *),
			"failed", RGBColor[1, 0.270588, 0] (* orangered *),
			"proved", RGBColor[0, 0.780392, 0.54902] (* turquoiseblue *),
			_, Black],
		Switch[ type,
			"prfsit", Disk[ pos, 0.1],
			"terminalNode", Map[ (pos + 0.1*#)&, Rectangle[ {-Sqrt[Pi]/2, -Sqrt[Pi]/2}, {Sqrt[Pi]/2, Sqrt[Pi]/2}]],
			_, Polygon[ Map[ (pos + 0.125*#)&, {{0,1}, {Cos[7*Pi/6], Sin[7*Pi/6]}, {Cos[11*Pi/6], Sin[11*Pi/6]}}]]],
		{Black, Dynamic[ Text[ 
			Hyperlink[ 
				Switch[ type, 
					"prfsit", "?",
					"andNode", "\[Wedge]",
					"orNode", "\[Vee]",
					"terminalNode", Switch[ status, "proved", "\[CheckmarkedBox]", "disproved", "\[Times]", "failed", "\[WarningSign]", _, "\[DownQuestion]"]], 
				{CurrentValue[ $TMAproofNotebook, "NotebookFileName"], id},
				BaseStyle -> {FontSize -> 14}], pos]]}
	}
makeNode[ args___] := unexpected[ makeNode, {args}]

(* ::Subsubsection:: *)
(* makeInitialProofObject *)

makeInitialProofObject[ goal_, kb_, rules_, strategy_] :=
	PRFOBJ$[
		PRFINFO$[ "ID" -> "Initial", goal, kb],
		PRFSIT$[ "ID" -> "Initial", goal, kb, "pending", "InferenceRules" -> preprocessRules[ strategy, rules], "Strategy" -> strategy]
	]
makeInitialProofObject[ args___] := unexpected[ makeInitialProofObject, {args}]


(* ::Subsubsection:: *)
(* makeInitialProofNotebook *)

makeInitialProofNotebook[ p_PRFOBJ$] :=
    Module[ { cells, t, nb},
        cells = proofObjectToCell[ p];
        $proofInProgressMarker = {Cell[BoxData[
        				DynamicBox[ ToBoxes[ Graphics[{Circle[{0, 0}, 1],
        					Table[Text[ToString[t], 0.8*{Cos[Pi/2 - (Pi/6)*t], Sin[Pi/2 - (Pi/6)*t]}, BaseStyle -> {FontSize -> 5}], {t, 1, 12}],
        					{Thick, Line[{{0, 0}, {Cos[Pi/2 - 2*Pi*Clock[]], Sin[Pi/2 - 2*Pi*Clock[]]}}],
        						Line[{{0, 0}, {Cos[Pi/4 - 2*Pi*Clock[]], Sin[Pi/4 - 2*Pi*Clock[]]}}]},
        					{Hue[ Clock[], 1, Clock[]], Opacity[0.5], Disk[{0, 0}, 1, {Pi/2 - 2*Pi*Clock[], Pi/4 - 2*Pi*Clock[]}]},
        					{White, Disk[{0, 0}, 0.7]}}, ImageSize -> {50, 50}], 
        					StandardForm], ImageSizeCache -> {50., {23., 27.}}]],
        				"Output", TextAlignment -> Center]};
        nb = NotebookPut[
            	Notebook[ cells, Visible -> False, StyleDefinitions -> FileNameJoin[{"Theorema", "Proof.nb"}]]];
        nb
    ]
makeInitialProofNotebook[ args___] := unexpected[ makeInitialProofNotebook, {args}]


(* ::Subsubsection:: *)
(* makeInitialProofTree *)

makeInitialProofTree[ ] := {{"Initial", "pending", "prfsit"}}
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

proofObjectToCell[ p_PRFOBJ$] := 
	Module[{ cellList = proofObjectToCell[ p[[1]]]},
		Join[ cellList, proofObjectToCell[ p[[2]]]]
	]
proofObjectToCell[ PRFINFO$[ id:("ID" -> "Initial"), goal_, kb_]] := proofStepText[ id, "Initial", $Language, goal, kb]
proofObjectToCell[ PRFSIT$[ id:("ID" -> _), g_, ___]] := proofStepText[ id, "Proof Situation", $Language, g]
	
proofObjectToCell[ args___] := unexpected[ proofObjectToCell, {args}]


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

preprocessRules[ s_, r_] := r
preprocessRules[ args___] := unexpected[ preprocessRules, {args}]


(* ::Section:: *)
(* Package Initialization *)

initProver[]

End[]

EndPackage[]