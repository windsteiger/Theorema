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
        appendEnvironmentFormula[x, newLab];
    ]
processEnvironment[args___] := unexcpected[ processEnvironment, {args}]

inEnvironment[] := Length[$environmentLabels]>0
inEnvironment[args___] := unexcpected[ inEnvironment, {args}]

adjustFormulaLabel[nb_NotebookObject] := 
	Module[{cellTags,cellID,newCellTags}, 
		SelectionMove[nb, All, EvaluationCell];
        {cellTags,cellID} = {CellTags,CellID} /. Options[NotebookSelection[nb], {CellTags,CellID}];
		(*
		 * Make sure we have a list of CellTags
		 *)
		cellTags = Flatten[{cellTags}];
		(*
		 * We need CellID as String
		 *)
		cellID = ToString[cellID];
        (*
         * Replace unlabeled formula with counter.
         *)
         If[cellTags=={$initLabel} || cellTags=={},
         	cellTags = newFormulaLabel[nb];
         	,
         	True
         ];
        (*
         * Relabel Cell and hide CellTags.
         *)
        newCellTags = relabelCell[nb,cellTags,cellID];
        SelectionMove[nb, After, Cell];
        newCellTags
	]
adjustFormulaLabel[args___]	:= unexpected[adjustFormulaLabel,{args}]

relabelCell[nb_NotebookObject, cellTags_List, cellID_String] :=
	Module[{newFrameLabel,newCellTags,cleanCellTags,duplicateCellTags},
		(* Perform check, weather are the given CellTags unique in the documment. *)
		duplicateCellTags = findDuplicateCellTags[nb,cellTags];
		If[duplicateCellTags===None,
				True
			,
				DialogInput[Column[{translate["notUniqueLabel"] <> StringJoin @@ Riffle[duplicateCellTags,$labelSeparator], Button["OK", DialogReturn[True]]}]];
				True
		];
	    (* Was the cell allready labeled by its CellID or $initLabel? Than remove CellID or $initLabel from CellTags list. *)
		cleanCellTags = Select[cellTags, # != cellID && # != $initLabel  & ];
		(* Join list of CellTags, use $labelSeparator. *)
		newFrameLabel = StringJoin @@ Riffle[cleanCellTags,$labelSeparator];
		(* Put newFrameLabel in brackets. *)
		newFrameLabel = "("<>newFrameLabel<>")";
		(* Keep cleaned CellTags and add CellID *)
		newCellTags = Join[{cellID},cleanCellTags];
		SetOptions[NotebookSelection[nb], CellFrameLabels->{{None,newFrameLabel},{None,None}}, CellTags->newCellTags, ShowCellTags->False];
		newCellTags
	]
relabelCell[args___] := unexpected[relabelCell,{args}]

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
uniqueLabel[args___] := unexpected[uniqueLabelCheck,{args___}]

newFormulaLabel[nb_NotebookObject] := 
	Module[{newFormulaCounter},
		(* Find highest value of any automatically counted formula. *)
		newFormulaCounter = formulaCounter[nb]+1;
		(* Construct new CellTags with value of the incremented formulaCounter as a list. *)
		newCellTags = {ToString[newFormulaCounter]};
		(* Introduce new cell option FormulaCounter with incremented value. *)
		SetOptions[NotebookSelection[nb], FormulaCounter->newFormulaCounter];
		newCellTags
	]
newFormulaLabel[args___] := unexpected[ newFormulaLabel, {args}]

appendEnvironmentFormula[form_, lab_] := 
	Module[{}, 
		$environmentFormulae = ReplacePart[$environmentFormulae, 1->Append[First[$environmentFormulae], {form, lab}]]
	]
appendEnvironmentFormula[args___] := unexpected[ appendEnvironmentFormula, {args}]
		
initSession[] := 
	Module[{}, 
		$environmentLabels = {};
		$environmentFormulaCounters = {};
		$environmentFormulae = {};
		$tmaEnv = {};
	];
initSession[args___] := unexpected[ initSession, {args}]

currentEnvironment[] := First[$environmentLabels]
currentEnvironment[args___] := unexpected[ currentEnvironment, {args}]

currentFormulae[] := First[$environmentFormulae]
currentFormulae[args___] := unexpected[ currentFormulae, {args}]

currentCounter[] := First[$environmentFormulaCounters]
currentCounter[args___] := unexpected[ currentCounter, {args}]

formulaCounter[nb_NotebookObject] :=
	Module[{max,rawNotebook,counterValues},
		max = 0;
		rawNotebook = NotebookGet[nb];
		(* Is FormulaCounter property assigned to any cell?. *)
		If[Count[rawNotebook,FormulaCounter,Infinity]>0,
				(* If so, select all such values. *)
				counterValues = Cases[rawNotebook,Cell[___,FormulaCounter -> counter_,___] -> counter, Infinity];
				(* Find maximum. *)
				max = Max[counterValues];
			,
				True;
		];
		max
	]
formulaCounter[args___] := unexpected[ formulaCounter, {args}]
 
currentCounterLabel[] := ToString[currentCounter[]]
currentCounterLabel[args___] := unexpected[ currentCounterLabel, {args}]

incrementCurrentCounter[] := 
	Module[{},
		$environmentFormulaCounters = ReplacePart[$environmentFormulaCounters, 1->currentCounter[]+1]
	]
incrementCurrentCounter[args___] := unexpected[ incrementCurrentCounter, {args}]

DEFINITION := openEnvironment["DEF"];

openEnvironment[type_] :=
    Module[{},
        PrependTo[$environmentFormulaCounters, 0];
        PrependTo[$environmentFormulae, {}];
        PrependTo[$environmentLabels, type];
        SetOptions[$FrontEnd, DefaultNewCellStyle -> "FormalTextInputFormula"];
        Begin["Theorema`Language`"];
    ]
openEnvironment[args___] := unexpected[ openEnvironment, {args}]

closeEnvironment[] := 
	Module[{},
		End[];
		updateEnv[ currentEnvironment[], currentFormulae[]];
		$environmentFormulaCounters = Rest[$environmentFormulaCounters];
        $environmentFormulae = Rest[$environmentFormulae];
        $environmentLabels = Rest[$environmentLabels];
        SetOptions[$FrontEnd, DefaultNewCellStyle -> "Input"];
        updateKBBrowser[];
	]
closeEnvironment[args___] := unexpected[ closeEnvironment, {args}]

updateEnv[ type_, form_] :=
    PrependTo[ $tmaEnv, {type, form}]
updateEnv[args___] := unexpected[ updateEnv, {args}]



(* ::Section:: *)
(* Computation *)

processComputation[\[GraySquare]] := (closeComputation[];)
processComputation[x_] := x
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

plus$TM /; activeComputation["plus"] = Plus
times$TM /; activeComputation["times"] = Times
set$TM /; activeComputation["equal"] = equal

End[]

(* ::Section:: *)
(* end of package *)

initSession[];
  
End[] (* End Private Context *)

EndPackage[];