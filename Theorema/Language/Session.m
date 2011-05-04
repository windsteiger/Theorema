(* Theorema 
    Copyright (C) 2010 The Theorema Group

    This file is part of Theorema.2
    
    Theorema.2 is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Theorema.2 is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*)

BeginPackage["Theorema`Language`Session`"];

Needs["Theorema`Common`"];
Needs["Theorema`Interface`Language`"];

Begin["`Private`"] (* Begin Private Context *) 


(* ::Section:: *)
(* Preprocessing *)

processEnvironment[\[GraySquare]] :=
    (closeEnvironment[];
     SelectionMove[EvaluationNotebook[], After, EvaluationCell];)

processEnvironment[x_] :=
    Module[ {nb = EvaluationNotebook[], newLab},
        newLab = adjustFormulaLabel[nb];
        updateKnowledgeBase[x, newLab];
    ]
processEnvironment[args___] := unexcpected[ processEnvironment, {args}]

inEnvironment[] := Length[$environmentLabels]>0
inEnvironment[args___] := unexcpected[ inEnvironment, {args}]

adjustFormulaLabel[nb_NotebookObject] := 
	Module[{cellTags,cellID,newCellTags, cleanCellTags}, 
		SelectionMove[nb, All, EvaluationCell];
        {cellTags,cellID} = {CellTags,CellID} /. Options[NotebookSelection[nb], {CellTags,CellID}];
		(*
		 * Make sure we have a list of CellTags
		 *)
		cellTags = Flatten[{cellTags}];
		(*
		 * Remove any automated labels (begins with "CellID_").
		 * Remove initLabel
		 *)
		cleanCellTags = Select[cellTags, Length[StringPosition[#, "CellID_"]] == 0 && # != $initLabel &];
        (*
         * Replace unlabeled formula with counter.
         *)
         If[Length[cleanCellTags]==0,
         	cleanCellTags = automatedFormulaLabel[nb];
         	,
         	True
         ];
        (*
         * Relabel Cell and hide CellTags.
         *)
        newCellTags = relabelCell[nb,cleanCellTags,cellID];
        SelectionMove[nb, After, Cell];
        newCellTags
	]
adjustFormulaLabel[args___]	:= unexpected[adjustFormulaLabel,{args}]

relabelCell[nb_NotebookObject, cellTags_List, cellID_Integer] :=
	Module[{newFrameLabel,newCellTags,duplicateCellTags},
		(* Perform check, weather are the given CellTags unique in the documment. *)
		duplicateCellTags = findDuplicateCellTags[nb,cellTags];
		If[duplicateCellTags===None,
				True
			,
				DialogInput[Column[{translate["notUniqueLabel"] <> StringJoin @@ Riffle[duplicateCellTags,$labelSeparator], Button["OK", DialogReturn[True]]}]];
				True
		];
		(* Join list of CellTags, use $labelSeparator. *)
		newFrameLabel = StringJoin @@ Riffle[cellTags,$labelSeparator];
		(* Put newFrameLabel in brackets. *)
		newFrameLabel = "("<>newFrameLabel<>")";
		(* Keep cleaned CellTags and add CellID *)
		newCellTags = Join[{getCellIDLabel[cellID]},cellTags];
		SetOptions[NotebookSelection[nb], CellFrameLabels->{{None,newFrameLabel},{None,None}}, CellTags->newCellTags, ShowCellTags->False];
		newCellTags
	]
relabelCell[args___] := unexpected[ relabelCell,{args}]

getCellIDLabel[cellID_Integer] :=
	Module[{},
		"CellID_" <> ToString[cellID]
	]
getCellIDLabel[args___] := unexpected[ getCellIDLabel,{args}]

findDuplicateCellTags[nb_NotebookObject, cellTags_List] :=
	Module[{rawNotebook,allCellTags,selectedCellTags,duplicateCellTags},
		rawNotebook = NotebookGet[nb];
		(* Collect all CellTags from document. *)
		allCellTags = Flatten[Cases[rawNotebook,Cell[___,CellTags -> tags_,___] -> tags, Infinity]];
		(* We look only for the duplicates to elements of current CellTags list.*)
		selectedCellTags = Select[allCellTags,MemberQ[cellTags,#] &];
		(* Are there more elements (clean cellTags as duplicate might appear even in one cell CellTags)? *)
		(* Check if CellTags are unique in curent Notebook. *)
		If[Length[selectedCellTags] > Length[DeleteDuplicates[cellTags]],
				(* If not select and return duplicate Labels, *)
				duplicateCellTags = Cases[Select[Tally[selectedCellTags],uniqueLabel[#]==False &],{cellTag_,_} -> cellTag]
			,
				(* else return None. *)
				None
		]
	]
findDuplicateCellTags[args___] := unexpected[findDuplicateCellTags,{args}]

uniqueLabel[{_,occurences_Integer}] :=
	If[occurences == 1,
		True,
		False
	]
uniqueLabel[args___] := unexpected[uniqueLabel,{args}]


(* ::Section:: *)
(* Region Title *)

(* ::Section:: *)
(* Region Title *)

(* ::Section:: *)
(* Region Title *)

automatedFormulaLabel[nb_NotebookObject] := 
	Module[{formulaCounter, newCellTags},
		incrementFormulaCounter[nb];
		(* Find highest value of any automatically counted formula. *)
		formulaCounter = getFormulaCounter[nb];
		(* Construct new CellTags with value of the incremented formulaCounter as a list. *)
		newCellTags = {ToString[formulaCounter]}
	]
automatedFormulaLabel[args___] := unexpected[ automatedFormulaLabel, {args}]

updateKnowledgeBase[ form_, lab_] :=
    $tmaEnv = Union[ $tmaEnv, {{lab, form}}, SameTest -> (#1[[1]]===#2[[1]]&) ]
updateKnowledgeBase[args___] := unexpected[ updateKnowledgeBase, {args}]

		
initSession[] :=
    Module[ {},
        $environmentLabels = {};
        $tmaEnv = {};
        $formulaCounterName = "TheoremaFormulaCounter";
    ]
initSession[args___] := unexpected[ initSession, {args}]

currentEnvironment[] := First[$environmentLabels]
currentEnvironment[args___] := unexpected[ currentEnvironment, {args}]

incrementFormulaCounter[nb_NotebookObject] :=
	Module[{formulaCounter},
		formulaCounter = getFormulaCounter[nb];
		formulaCounter++;
		(* Save Incremented formulaCounter to the notebook options. *)
		SetOptions[nb, CounterAssignments -> {{$formulaCounterName -> formulaCounter}}]
	]
incrementFormulaCounter[args___] := unexpected[ incrementFormulaCounter, {args}]

getFormulaCounter[nb_NotebookObject] :=
	Module[{formulaCounter},
		(* Extract theoremaFormulaCounter from the options of the notebook. *)
		formulaCounter = 
			$formulaCounterName /. Flatten[
				(* Extract CounerAssignments from the options of the notebook. *)
				{CounterAssignments } /. Options[nb, CounterAssignments]
			]
	]
getFormulaCounter[args___] := unexpected[ getFormulaCounter, {args}]
 
DEFINITION := openEnvironment["DEF"];

openEnvironment[type_] :=
    Module[{},
        PrependTo[$environmentLabels, type];
        SetOptions[$FrontEnd, DefaultNewCellStyle -> "FormalTextInputFormula"];
        Begin["Theorema`Language`"];
    ]
openEnvironment[args___] := unexpected[ openEnvironment, {args}]

closeEnvironment[] := 
	Module[{},
		End[];
        $environmentLabels = Rest[$environmentLabels];
        SetOptions[$FrontEnd, DefaultNewCellStyle -> "Input"];
        updateKBBrowser[];
	]
closeEnvironment[args___] := unexpected[ closeEnvironment, {args}]


(* ::Section:: *)
(* Computation *)

processComputation[\[GraySquare]] := (closeComputation[];)
processComputation[x_] := Module[ {},
	printComputationInfo[];
	x
]
processComputation[args___] := unexcpected[ processComputation, {args}]

COMPUTE := openComputation[];

openComputation[] :=
  Module[ {},
  	If[ !inComputation[],
  	  SetOptions[$FrontEnd, DefaultNewCellStyle -> "Computation"];
      Begin["Theorema`Computation`"];
  	]
  ]
openComputation[args___] := unexcpected[ openComputation, {args}]


inComputation[] := Context[] === "Theorema`Computation`"
inComputation[args___] := unexcpected[ inComputation, {args}]

closeComputation[] := Module[{},
	End[];
  	SetOptions[$FrontEnd, DefaultNewCellStyle -> "Input"];
	]
closeComputation[args___] := unexcpected[ closeComputation, {args}]

(* ::Section:: *)
(* Built-in computation *)

Begin["Theorema`Computation`"]

activeComputation[_] := False
activeComputationKB[_] := False

plus$TM /; activeComputation["plus"] = Plus
times$TM /; activeComputation["times"] = Times
set$TM /; activeComputation["equal"] = equal

End[]

(* ::Section:: *)
(* end of package *)

initSession[];
  
End[] (* End Private Context *)

EndPackage[];