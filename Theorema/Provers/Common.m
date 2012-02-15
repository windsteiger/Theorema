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

callProver[ prover_, goal_, kb_] :=
	Module[{},
		$TMAproofObject = makeInitialProofObject[ goal, kb, prover];
		$TMAproofNotebook = makeInitialProofNotebook[ $TMAproofObject];
		{ $Failed, $TMAproofObject}
	]
callProver[ args___] := unexpected[ callProver, {args}]

showProofNavigation[ p_PRFOBJ$] :=
	Module[{},
		TreeForm[ p, 3,
			VertexRenderingFunction -> (Inset[ Hyperlink[Short[#2], {CurrentValue[ $TMAproofNotebook, "NotebookFileName"], None}], #1] &),
			AspectRatio -> 3/4, ImageSize -> {600,800}]
	]
showProofNavigation[ p_] := ""
showProofNavigation[ args___] := unexpected[ showProofNavigation, {args}]


(* ::Subsubsection:: *)
(* makeInitialProofObject *)

makeInitialProofObject[ goal_, kb_, prover_] :=
	PRFOBJ$[
		PRFINFO$[ "Initial", goal, kb],
		PRFSIT$[ goal, kb, {}, "pending", "InferenceRules" -> inferenceRules[ prover]]
	]
makeInitialProofObject[ args___] := unexpected[ makeInitialProofObject, {args}]


(* ::Subsubsection:: *)
(* Region Title *)
makeInitialProofNotebook[ p_PRFOBJ$] :=
    Module[ { cells, t, nb},
        cells = proofObjectToCell[ p];
        nb = NotebookPut[
            	Notebook[ Append[ cells,
            		Cell[BoxData[
        				DynamicBox[ ToBoxes[ Graphics[{
        					Circle[{0, 0}, 1],
        					Table[ Text[ ToString[t], 0.9*{Cos[Pi/2 - (Pi/6)*t], Sin[Pi/2 - (Pi/6)*t]}], {t, 1, 12}],
        					{Thick, Line[{{0, 1}, {0, 0}, {Cos[Pi/2 - 2*Pi*Clock[]], Sin[Pi/2 - 2*Pi*Clock[]]}}]},
        					{Hue[5/8, 1, Clock[]], Opacity[0.5], Disk[{0, 0}, 1, {Pi/2, Pi/2 - 2*Pi*Clock[]}]}}], 
        					StandardForm], ImageSizeCache -> {360., {178., 181.}}]],
        				"Output", TextAlignment -> Center]], Visible -> False, StyleDefinitions -> FileNameJoin[{"Theorema", "Proof.nb"}]]];
        nb
    ]
makeInitialProofNotebook[ args___] := unexpected[ makeInitialProofNotebook, {args}]


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
proofObjectToCell[ PRFINFO$[ "Initial", goal_, kb_]] := 
	{textCell[ "We have to prove:"], 
     goalCell[ goal], 
     textCell[ "under the assumptions:"], 
     assumptionListCells[ kb, ",", "."]
     }
proofObjectToCell[ PRFSIT$[ g_, ___]] := 
	{textCell[ "In order to prove", referenceCell[ g], "we have to ..."]}
proofObjectToCell[ args___] := unexpected[ proofObjectToCell, {args}]

goalCell[ {k_, g_, t_}, punct_String:""] := 
	Cell[ BoxData[ RowBox[ {ToBoxes[ g], punct}]], "Goal", 
		CellFrameLabels->{{None, Cell[ t, "GoalLabel"]}, {None, None}}, 
		CellTags -> getCellIDLabel[ k]
	]
goalCell[ args___] := unexpected[ goalCell, {args}]

assumptionCell[ {k_, a_, t_}, punct_String:""] := 
	Cell[ BoxData[ RowBox[ {ToBoxes[ a], punct}]], "Assumption", 
		CellFrameLabels->{{None, Cell[ t, "AssumptionLabel"]}, {None, None}}, 
		CellTags -> getCellIDLabel[ k]
	]
assumptionCell[ args___] := unexpected[ assumptionCell, {args}]

assumptionListCells[ {f___, l_}, sep_String, punct_String] :=
	Module[{initial, term},
		initial = Map[ assumptionCell[ #, sep]&, {f}];
		term = assumptionCell[ l, punct];
		Cell[ CellGroupData[ Append[ initial, term]]]
	]
assumptionListCells[ args___] := unexpected[ assumptionListCells, {args}]

textCell[ t__] := Cell[ TextData[ Riffle[ {t}, " "]], "Text"]
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