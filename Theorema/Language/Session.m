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

BeginPackage["Theorema`Interface`Session`"];
(* Exported symbols added here with SymbolName::usage *)  

preprocessTheoremaExpression::usage = "The standard preprocessor";
DEFINITION::usage = "Theorema definition environment";
\[GraySquare]::usage = "End of environment marker";
initSession::usage = "Initialize session variables";

Needs["Theorema`System`Messages`"];

Begin["`Private`"] (* Begin Private Context *) 


(* ::Section:: *)
(* Preprocessing *)


(* ::Subsubsection:: *)
(* preprocessTheoremaExpression *)

SetAttributes[preprocessTheoremaExpression,HoldAll];

preprocessTheoremaExpression[expr_]:=preprocessTheoremaExpressionHold[Hold[expr]];

preprocessTheoremaExpressionHold[expr_]:=markVariables[globalTyping[freshNames[expr]]];
preprocessTheoremaExpressionHold[expr_]:=
	Which[inEnvironment[],
		processEnvironment[ReleaseHold[expr]],
		True,
		ReleaseHold[expr]
	]

processEnvironment[\[GraySquare]] := closeEnvironment[]

processEnvironment[x_] :=
    Module[ {nb = InputNotebook[], newLab},
        newLab = adjustFormulaLabel[nb];
        appendEnvironmentFormula[x, newLab];
    ]

inEnvironment[] := Length[$environmentLabels]>0

adjustFormulaLabel[nb_NotebookObject] := 
	Module[{cl}, 
		SelectionMove[nb, Previous, Cell];
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
		$Pre = preprocessTheoremaExpression;
	]

currentEnvironment[] := First[$environmentLabels]

currentFormulae[] := First[$environmentFormulae]

currentCounter[] := First[$environmentFormulaCounters]

currentCounterLabel[] := ToString[currentCounter[]]

incrementCurrentCounter[] := 
	Module[{},
		$environmentFormulaCounters = ReplacePart[$environmentFormulaCounters, 1->currentCounter[]+1]
	]

DEFINITION[label_] := openEnvironment["DEF", label];

openEnvironment[type_, label_] :=
    Module[{},
        PrependTo[$environmentFormulaCounters, 0];
        PrependTo[$environmentFormulae, {}];
        PrependTo[$environmentLabels, {type,type<>":"<>label}];
    ]

closeEnvironment[] := 
	Module[{env=currentEnvironment[]},
		tmaEnv[env[[1]],env[[2]]] = currentFormulae[];
		$environmentFormulaCounters = Rest[$environmentFormulaCounters];
        $environmentFormulae = Rest[$environmentFormulae];
        $environmentLabels = Rest[$environmentLabels];
        Theorema`Interface`GUI`updateKBBrowser[];
	]

(* ::Section:: *)
(* end of package *)
  
End[] (* End Private Context *)

EndPackage[];