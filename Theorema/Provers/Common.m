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
	Module[{po},
		po = makeProofObject[ goal, kb, prover];
		{ $Failed, po}
	]
callProver[ args___] := unexpected[ callProver, {args}]


(* ::Subsubsection:: *)
(* makeProofObject *)

makeProofObject[ goal_, kb_, prover_] :=
	PROOFOBJ$[ {goal, kb, "InferenceRules" -> inferenceRules[ prover]}]
makeProofObject[ args___] := unexpected[ makeProofObject, {args}]


(* ::Subsubsection:: *)
(* displayProof *)

displayProof[ p_PROOFOBJ$] :=
	Module[{nb, cells},
		cells = proofObjectToCell[ p];
		nb = Notebook[ cells, StyleDefinitions -> FileNameJoin[{"Theorema", "Proof.nb"}]];
		NotebookPut[ nb];
	]
displayProof[ args___] := unexpected[ displayProof, {args}]


(* ::Subsubsection:: *)
(* proofNotebook *)

proofNotebook[ p_PROOFOBJ$] :=
	Module[{cells},
		cells = proofObjectToCell[ p];
		DocumentNotebook[ cells, StyleDefinitions -> "Proof.nb"]
	]
proofNotebook[ args___] := unexpected[ proofNotebook, {args}]

(* ::Subsubsection:: *)
(* proofObjectToCell *)

proofObjectToCell[ p_PROOFOBJ$] := { textCell[ "We have to prove:"], goalCell[ p[[1, 1]]], textCell[ "under the assumptions:"], CellGroup[ Map[ assumptionCell, p[[1, 2]]]]}
proofObjectToCell[ args___] := unexpected[ proofObjectToCell, {args}]

goalCell[ {k_, g_, t_}] := Cell[ BoxData[ ToBoxes[ g]], "Goal", CellFrameLabels->{{None, t}, {None, None}}]
goalCell[ args___] := unexpected[ goalCell, {args}]

assumptionCell[ {k_, a_, t_}] := Cell[ BoxData[ ToBoxes[ a]], "Assumption", CellFrameLabels->{{None, t}, {None, None}}]
assumptionCell[ args___] := unexpected[ assumptionCell, {args}]

textCell[ t_] := Cell[ t, "Text"]
textCell[ args___] := unexpected[ textCell, {args}]


End[]

EndPackage[]