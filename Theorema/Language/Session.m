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
(* Exported symbols added here with SymbolName::usage *)  

Needs["Theorema`Common`"];

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
	Module[{cl}, 
		SelectionMove[nb, All, EvaluationCell];
        cl = CellTags /. Options[NotebookSelection[nb], CellTags];
        Switch[cl,
        	{_,_},
        	cl = newFormulaLabel[nb,cl]
        ];
        SelectionMove[nb, After, Cell];
        cl
	]
adjustFormulaLabel[args___]	:= unexpected[adjustFormulaLabel,{args}]

newFormulaLabel[nb_NotebookObject, {_, lab_}] := 
	Module[{newLab},		
        newLab = currentEnvironment[][[2]]<>"_"<>If[lab==="???",incrementCurrentCounter[];currentCounterLabel[],lab];
        SetOptions[NotebookSelection[nb], CellTags->newLab];
        newLab		
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
	]
initSession[args___] := unexpected[ initSession, {args}]

currentEnvironment[] := First[$environmentLabels]
currentEnvironment[args___] := unexpected[ currentEnvironment, {args}]

currentFormulae[] := First[$environmentFormulae]
currentFormulae[args___] := unexpected[ currentFormulae, {args}]

currentCounter[] := First[$environmentFormulaCounters]
currentCounter[args___] := unexpected[ currentCounter, {args}]

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

plus$TM /; activeComputation[Plus] = Plus

End[]

(* ::Section:: *)
(* end of package *)

initSession[];
  
End[] (* End Private Context *)

EndPackage[];