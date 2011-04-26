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

inEnvironment[] := Length[$environmentLabels]>0

adjustFormulaLabel[nb_NotebookObject] := 
	Module[{cl,cid}, 
		SelectionMove[nb, All, EvaluationCell];
        {cl,cid} = {CellTags,CellID} /. Options[NotebookSelection[nb], {CellTags,CellID}];
        (*
         * Replace unlabeled formula with counter.
         *)
        If[cl=="???",
        	cl = newFormulaLabel[nb,cl],
        	true
        ];
        (*
         * If Cell is not labeled by its CellID, relabel it and hide cell tags..
         *)
        If[cl!=ToString[cid],
        	relabelCell[nb,cl,cid],
        	true
       	];
        SelectionMove[nb, After, Cell];
        cl
	]
adjustFormulaLabel[args___]	:= unexpected[adjustFormulaLabel,{args}]

relabelCell[nb_NotebookObject, cl_, cid_] :=
	Module[{newFrameLabel,newLabel},
		newFrameLabel = cl;
		newLabel = ToString[cid];
		SetOptions[NotebookSelection[nb], CellFrameLabels->{{{},newFrameLabel},{{},{}}}, CellTags->newLabel, ShowCellTags->False];
	]
	
relabelCell[args___] := unexpected[relabelCell,{args}]

newFormulaLabel[nb_NotebookObject, lab_] := 
	Module[{newLab},		
        (* newLab = currentEnvironment[][[2]]<>"_"<>If[lab==="???",incrementCurrentCounter[];currentCounterLabel[],lab]; *)
        newLab = If[lab==="???",incrementCurrentCounter[];currentCounterLabel[],lab];
        SetOptions[NotebookSelection[nb], CellTags->newLab];
        newLab		
	]
newFormulaLabel[args___] := unexpected[newFormulaLabel,{args}]

appendEnvironmentFormula[form_, lab_] := 
	Module[{}, 
		$environmentFormulae = ReplacePart[$environmentFormulae, 1->Append[First[$environmentFormulae], {form, lab}]]
	]
		
initSession[] := 
	Module[{}, 
		$environmentLabels = {};
		$environmentFormulaCounters = {};
		$environmentFormulae = {};
		$tmaEnv = {};
	]

currentEnvironment[] := First[$environmentLabels]

currentFormulae[] := First[$environmentFormulae]

currentCounter[] := First[$environmentFormulaCounters]

currentCounterLabel[] := ToString[currentCounter[]]

incrementCurrentCounter[] := 
	Module[{},
		$environmentFormulaCounters = ReplacePart[$environmentFormulaCounters, 1->currentCounter[]+1]
	]

DEFINITION := openEnvironment["DEF"];

openEnvironment[type_] :=
    Module[{},
        PrependTo[$environmentFormulaCounters, 0];
        PrependTo[$environmentFormulae, {}];
        PrependTo[$environmentLabels, type];
        Begin["Theorema`Language`"];
    ]

closeEnvironment[] := 
	Module[{},
		End[];
		updateEnv[ currentEnvironment[], currentFormulae[]];
		$environmentFormulaCounters = Rest[$environmentFormulaCounters];
        $environmentFormulae = Rest[$environmentFormulae];
        $environmentLabels = Rest[$environmentLabels];
        updateKBBrowser[];
	]

updateEnv[ type_, form_] :=
    PrependTo[ $tmaEnv, {type, form}]

(* ::Section:: *)
(* end of package *)

initSession[];
  
End[] (* End Private Context *)

EndPackage[];