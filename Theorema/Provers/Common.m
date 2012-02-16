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

Begin["`Private`"]


(* ::Subsubsection:: *)
(* callProver *)

$TMAproofTree = {};

callProver[ prover_, goal_, kb_] :=
	Module[{},
		$TMAproofObject = makeInitialProofObject[ goal, kb, prover];
		$TMAproofNotebook = makeInitialProofNotebook[ $TMAproofObject];
		$TMAproofTree = makeInitialProofTree[ ];
		Pause[1];
		$TMAproofTree = {{"Initial", "pending", "andNode"} -> {"new1", "pending", "prfsit"},
  			{"Initial", "pending", "andNode"} -> {"new2", "pending", "prfsit"}};
  		Pause[2];
  		$TMAproofTree = $TMAproofTree /. {"new2", _, _} -> {"new2", "pending", "andNode"};
  		AppendTo[ $TMAproofTree, {"new2", "pending", "andNode"} -> {"new3", "proved", "terminalNode"}];
  		Pause[2];
  		$TMAproofTree = $TMAproofTree /. {id_, "pending", "andNode"} -> {id, "proved", "andNode"};
		{$Failed, $TMAproofObject}
	]
callProver[ args___] := unexpected[ callProver, {args}]

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

makeInitialProofObject[ goal_, kb_, prover_] :=
	PRFOBJ$[
		PRFINFO$[ "Initial", goal, kb, "Initial"],
		PRFSIT$[ goal, kb, {}, "pending", "InferenceRules" -> inferenceRules[ prover]]
	]
makeInitialProofObject[ args___] := unexpected[ makeInitialProofObject, {args}]


(* ::Subsubsection:: *)
(* makeInitialProofNotebook *)
makeInitialProofNotebook[ p_PRFOBJ$] :=
    Module[ { cells, t, nb},
        cells = proofObjectToCell[ p];
        nb = NotebookPut[
            	Notebook[ Append[ cells,
            		Cell[BoxData[
        				DynamicBox[ ToBoxes[ Graphics[{Circle[{0, 0}, 1],
        					Table[Text[ToString[t], 0.9*{Cos[Pi/2 - (Pi/6)*t], Sin[Pi/2 - (Pi/6)*t]}], {t, 1, 12}],
        					{Thick, Line[{{0, 0}, {Cos[Pi/2 - 2*Pi*Clock[]], Sin[Pi/2 - 2*Pi*Clock[]]}}],
        						Line[{{0, 0}, {Cos[Pi/4 - 2*Pi*Clock[]], Sin[Pi/4 - 2*Pi*Clock[]]}}]},
        					{Hue[5/8, 1, Clock[]], Opacity[0.5], Disk[{0, 0}, 1, {Pi/2 - 2*Pi*Clock[], Pi/4 - 2*Pi*Clock[]}]},
        					{White, Disk[{0, 0}, 0.8]}}], 
        					StandardForm], ImageSizeCache -> {360., {178., 181.}}]],
        				"Output", TextAlignment -> Center]], Visible -> False, StyleDefinitions -> FileNameJoin[{"Theorema", "Proof.nb"}]]];
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
proofObjectToCell[ PRFINFO$[ "Initial", goal_, kb_, id_]] :=
    Block[ {$prfStepID = id},
        {textCell[ "We have to prove:"], 
         goalCell[ goal], 
         textCell[ "under the assumptions:"], 
         assumptionListCells[ kb, ",", "."]
         }
    ]
proofObjectToCell[ PRFSIT$[ g_, ___]] := 
	{textCell[ "In order to prove", referenceCell[ g], "we have to ..."]}
proofObjectToCell[ args___] := unexpected[ proofObjectToCell, {args}]

goalCell[ {k_, g_, t_}, punct_String:""] := 
	Cell[ BoxData[ RowBox[ {ToBoxes[ g], punct}]], "Goal", 
		CellFrameLabels->{{None, Cell[ t, "GoalLabel"]}, {None, None}}, 
		CellTags -> {getCellIDLabel[ k], $prfStepID}
	]
goalCell[ args___] := unexpected[ goalCell, {args}]

assumptionCell[ {k_, a_, t_}, punct_String:""] := 
	Cell[ BoxData[ RowBox[ {ToBoxes[ a], punct}]], "Assumption", 
		CellFrameLabels->{{None, Cell[ t, "AssumptionLabel"]}, {None, None}}, 
		CellTags -> {getCellIDLabel[ k], $prfStepID}
	]
assumptionCell[ args___] := unexpected[ assumptionCell, {args}]

assumptionListCells[ {f___, l_}, sep_String, punct_String] :=
	Module[{initial, term},
		initial = Map[ assumptionCell[ #, sep]&, {f}];
		term = assumptionCell[ l, punct];
		Cell[ CellGroupData[ Append[ initial, term]]]
	]
assumptionListCells[ args___] := unexpected[ assumptionListCells, {args}]

textCell[ t__] := Cell[ TextData[ Riffle[ {t}, " "]], "Text", CellTags -> {$prfStepID}]
textCell[ args___] := unexpected[ textCell, {args}]

referenceCell[ {k_, form_, label_}] :=
	With[{ tag = getCellIDLabel[k]},
        Cell[ BoxData[ ToBoxes[
            Button[ Tooltip[ Mouseover[ Style[ label, "Reference"], Style[ label, "ReferenceHover"]], form],
            	Module[ {cell},
        			NotebookFind[ SelectedNotebook[], tag, Previous, CellTags, AutoScroll -> False];
        			cell = NotebookRead[ SelectedNotebook[]];
                	CreateDialog[{cell, CancelButton["OK", NotebookClose[ButtonNotebook[]]]}]], Appearance->None]
        ]]]
	]
referenceCell[ args___] := unexpected[ referenceCell, {args}]



End[]

EndPackage[]