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

BeginPackage["Theorema`Computation`Common`"]

Needs[ "Theorema`Common`"]
Needs[ "Theorema`Language`"]

Begin["`Private`"]

(*
f[x_] /; active[f] && condition[x > 0 && x < 0, f, {x}] := result[x^2]
g[x_] /; active[g] && condition[x > 0, g, {x}] := result[2 x + 3]
ghi[x_] /; active[ghi] && condition[x > 0 && x > -5, ghi, {x}] := result[2 x + 3]
h[xtest_, y_, z_] /; active[h] && condition[h, {xtest, y, z}] := result[xtest^2 + y^2 + z^2]
r[x_] /; active[r] && condition[x > 0, r, {x}] := result[x^3]

s2[x_] /; active[s] && condition[x > 0 && t1[x] < t1[x + 1], s, {x}] :=result[x]
s[x_] /; active[s] && condition[x > 0 && t1[x] < 0, s, {x}] := result[x]
t1[x_] /; active[t1] && condition[t1, {x}] := result[x^2]
t[x_] /; active[t] && condition[t, {x}] := result[r[x]]

test1[0] /; active[test1] && condition[test1, {0}] := result[0]
test1[x_] /; active[test1] && condition[test2[x] > 0, test1, {x}] := result[x + test1[x - 1]]
test2[x_] /; active[test2] && condition[test2, {x}] := result[x]

a1[x_] /; active[a1] && condition[x > 0 && asdf[x] > 0, a1, {x}] := result[x^2]
 *)

SetAttributes[extr, HoldAll]
SetAttributes[condition, HoldAll]
SetAttributes[result, HoldAll]
SetAttributes[compute, HoldAll]


extr[x_] := {HoldForm[x]}
extr[And[x_, y__]] := ReleaseHold[Flatten[{HoldForm[HoldForm[x]], Map[HoldForm, HoldForm[y]]}]]

active[f_] :=
	Module[{}, 
		If[ToString[Definition[f]] != "Null", Return[True], Return[False]]
	] (* just checks if function is defined *)

condition[fct_, param_] :=
	Module[{},
		calculation = InsertInTrace[calculation, {Apply[HoldForm[fct], param]}, insertPosition];
  		AppendTo[insertPosition, 2];
  		True
  	]

condition[cond_, fct_, param_] := 
	Module[{condlist = extr[cond], c}, 
		calculation = InsertInTrace[calculation, {Apply[HoldForm[fct], param]}, insertPosition];
		AppendTo[insertPosition, 2]; 
  		calculation = InsertInTrace[calculation, {}, insertPosition]; 
  		AppendTo[insertPosition, 1];
  		For[i = 1, i <= Length[condlist], i++,
   			calculation = InsertInTrace[calculation, {}, insertPosition]; 
   			AppendTo[insertPosition, 1];
   			c = provecond[condlist[[i]]];
   			insertPosition = Most[insertPosition];
   			If[c === False,(* the current condition is not fulfilled *)
    			calculation = InsertInTrace[calculation, condlist[[i]], Append[insertPosition, 1]];
    			calculation = InsertInTrace[calculation, False, Append[insertPosition, Length[Extract[calculation, insertPosition]] + 1]];
    			insertPosition = Most[insertPosition]; 
    			calculation = InsertInTrace[calculation, {False, i}, insertPosition]; 
    			insertPosition = Most[insertPosition]; 
    			insertPosition[[Length[insertPosition]]] = insertPosition[[Length[insertPosition]]] + 1;
    			Return[False]
    		];
   			If[Not[TrueQ[c]],(* the current condition couldn't be checked if it is true or false *)
    			calculation = InsertInTrace[calculation, condlist[[i]], Append[insertPosition, 1]];
    			calculation = InsertInTrace[calculation, "undetermined", Append[insertPosition, Length[Extract[calculation, insertPosition]] + 1]];
    			insertPosition = Most[insertPosition]; 
    			calculation = InsertInTrace[calculation, {"undetermined", i}, insertPosition]; 
    			insertPosition = Most[insertPosition]; 
    			insertPosition[[Length[insertPosition]]] = insertPosition[[Length[insertPosition]]] + 1;
    			Return[False]
    		];
   			(* the current condition is fulfilled *)
   			calculation = InsertInTrace[calculation, condlist[[i]], Append[insertPosition, 1]];
   			calculation = InsertInTrace[calculation, True, Append[insertPosition, Length[Extract[calculation, insertPosition]] + 1]];
   			insertPosition[[Length[insertPosition]]] = i + 1;
   		];
  		insertPosition = Most[insertPosition]; 
  		calculation = InsertInTrace[calculation, {True, 0}, insertPosition];
   		insertPosition[[Length[insertPosition]]] = insertPosition[[Length[insertPosition]]] + 2;
   		Return[True]
   	]

provecond[cond_] := 
 	Module[{}, 
  		Return[ReleaseHold[cond]](*check condition with theorema proofer *)
  	]

InsertInTrace[calc_, toInsert_, pos_] := 
 	Module[{},
 		Insert[calculation, toInsert, pos]
 	]

result[body_] := 
 	Module[{v}, 
 		calculation = InsertInTrace[calculation, {HoldForm[body]}, insertPosition]; 
  		insertPosition = AppendTo[insertPosition, 2]; v = body; 
  		calculation = InsertInTrace[calculation, v, insertPosition]; 
  		insertPosition = Most[Most[insertPosition]]; 
  		insertPosition[[Length[insertPosition]]] = insertPosition[[Length[insertPosition]]] + 1;
  		Return[v]
  	]

compute[c_] := 
 	Module[{result},
 		calculation = {HoldForm[c]}; insertPosition = {2}; 
  		AppendTo[calculation, result = c]; 
  		NotebookWrite[EvaluationNotebook[], 
  			Cell[BoxData[ToBoxes[Button["Show Calculation", showcalc[calculation], 
  			ImageSize -> Automatic, Method -> "Queued"]]], "Output"]]; 
  		result
  	]

showcalc[calclist_] := 
 	Module[{cells}, 
 		cells = {Cell[CellGroupData[
 			Join[{Cell[BoxData[ToBoxes[First[calclist]]], "CalculationInput"]}, 
       			Map[subcompToCell, Drop[Drop[calclist, 1], -1]],
       			{Cell[BoxData[ToBoxes[Last[calclist]]], "CalculationInput"]}
       			]]]}; 
  		NotebookPut[Notebook[cells], StyleDefinitions -> getStyle];]

subcompToCell[{inp_, subcomp__, outp_}, level_: 0] := 
	Module[{},
		Print[level, " Subcomputation detected"];
		Print[subcomp]; 
  		Cell[CellGroupData[
    		Join[{Cell[BoxData[ToBoxes[inp]], "Subfct", createCellMargin[27 + 27*level]]}, 
     			subcompToCell[#, level + 1] & /@ {subcomp},
     				{Cell[BoxData[ToBoxes[outp]], "Subfct", CellLabel -> "=", createCellMargin[27 + 27*level]]}
     		]
     	]]
     ]

subcompToCell[{def_, {held_HoldForm, res_}}, level_: 0] := 
 	Module[{},
 		Print[level, " no conditions, simple "]; 
 		Cell[CellGroupData[
 			{Cell[BoxData[ToBoxes[def]], "Subfct", createCellMargin[27 + 27*level]], 
     		Cell[TextData["Function has no conditions"], "Text", createCellMargin[27 + 27*level]], 
     		Cell[CellGroupData[
     			{Cell[BoxData[ToBoxes[held]], "Subfct", createCellMargin[27 + 27*level]], 
        		Cell[BoxData[ToBoxes[res]], "Subfct", CellLabel -> "=", createCellMargin[27 + 27*level]]}
        	]]}
        ]]
	]

subcompToCell[{held_, {calc__}}, level_: 0] := 
	Module[{},
		Print[level, " complicated result"];
		Print[held]; 
  		Print[calc];
  		Print[level]; 
  		Cell[CellGroupData[
  			{Cell[BoxData[ToBoxes[held]], "Subfct", createCellMargin[27 + 27*level]], subcompToCell[{calc}, level + 1]}
  		]]
  	]

subcompToCell[{held_HoldForm, res_}, level_: 0] := 
	Module[{},
		Print[level, " just result"]; 
  		Cell[CellGroupData[
  			{Cell[BoxData[ToBoxes[held]], "Subfct", createCellMargin[27 + 27*level]], 
     		Cell[BoxData[ToBoxes[res]], "Subfct", CellLabel -> "=", createCellMargin[27 + 27*level]]}
     	]]
     ]

subcompToCell[{def_, {"undetermined", n_}, condlist_}, level_: 0] := 
	Module[{}, 
		Print[level, " a condition could not be evaluated to true or false"]; 
  		Cell[CellGroupData[
  			{Cell[BoxData[ToBoxes[def]], "Subfct", createCellMargin[27 + 27*level]], 
     		Cell[CellGroupData[
     			Join[
     				{Cell[TextData["Function cannot be applied because a condition could not be evaluated to true or false"], "Text", createCellMargin[27 + 27*level]]}, 
        			condToCell[#, level] & /@ condlist[[1 ;; n - 1]],
        			{condToCell[condlist[[n]]]}
        		]
        	]]}
        ]]
	]

condToCell[{cond_, "undetermined"}, level_: 0] := 
 	Module[{},
 		Print[cond]; 
  		Cell[CellGroupData[
  			{Cell[BoxData[ToBoxes[cond]], "CondNotFulfilled",createCellMargin[66 + 27*level], CellDingbat -> StyleBox["\[EmptySquare]", ShowStringCharacters -> False, StripOnInput -> False]], 
     		Cell[TextData["cannot be evaluated"], "CondNotFulfilled", createCellMargin[66 + 27*level]]}
     	]]
     ]

condToCell[{cond_, calc__, "undetermined"}, level_: 0] := 
 	Module[{},
 		Print["Second condlist ", cond]; 
  		Cell[CellGroupData[
  			Join[
  				{Cell[BoxData[ToBoxes[cond]], "CondNotFulfilled", createCellMargin[66 + 27*level], CellDingbat -> StyleBox["\[EmptySquare]", ShowStringCharacters -> False, StripOnInput -> False]]}, 
     			subcompToCell[#, level + 1] & /@ {calc}, 
     			{Cell[TextData["cannot be evaluated"], "CondNotFulfilled", createCellMargin[66 + 27*level]]}
     		]
     	]]
     ]

subcompToCell[{def_, {False, n_}, condlist_}, level_: 0] := 
 	Module[{},
 		Print[level, " conditions not fulfilled"]; 
  		Cell[CellGroupData[
  			{Cell[BoxData[ToBoxes[def]], "Subfct", createCellMargin[27 + 27*level]], 
     		Cell[CellGroupData[
       			Join[
       				{Cell[TextData["Function cannot be applied because a condition is not fulfilled"], "Text", createCellMargin[27 + 27*level]]}, 
        			condToCell[#, level] & /@ condlist[[1 ;; n - 1]], 
        			{condToCell[condlist[[n]]]}
        		]
        	]]}
        ]]
	]

condToCell[{cond_, False}, level_: 0] := 
	Module[{},
		Print[cond]; 
		Cell[CellGroupData[
			{Cell[BoxData[ToBoxes[cond]], "CondNotFulfilled",createCellMargin[66 + 27*level], CellDingbat -> StyleBox["\[WarningSign]", ShowStringCharacters -> False, StripOnInput -> False]], 
     		Cell[BoxData[ToBoxes[False]], "CondNotFulfilled", createCellMargin[66 + 27*level]]}
     	]]
     ]

condToCell[{cond_, calc__, False}, level_: 0] := 
	Module[{},
		Print["Second condlist ", cond]; 
  		Cell[CellGroupData[
    		Join[
    			{Cell[BoxData[ToBoxes[cond]], "CondNotFulfilled", createCellMargin[66 + 27*level], CellDingbat -> StyleBox["\[WarningSign]", ShowStringCharacters -> False, StripOnInput -> False]]}, 
     			subcompToCell[#, level + 1] & /@ {calc},
     			{Cell[BoxData[ToBoxes[False]], "CondNotFulfilled", createCellMargin[66 + 27*level]]}
     		]
     	]]
     ]

subcompToCell[{def_, {True, _}, condlist_, res_}, level_: 0] := 
	Module[{},
		Print[level, " conditions fulfilled"];
		Print[condlist]; 
  		Cell[CellGroupData[
  			{Cell[BoxData[ToBoxes[def]], "Subfct", createCellMargin[27 + 27*level]], 
     		Cell[CellGroupData[
       			Join[
       				{Cell[TextData["All conditions are fulfilled"], "Text", createCellMargin[27 + 27*level]]}, 
        			condToCell[#, level] & /@ condlist
        		]
        	]], 
     		Cell[CellGroupData[{subcompToCell[res, level + 1]}]]}
     	]] 
	]

condToCell[{cond_, True}, level_: 0] := 
	Module[{},
		Print[cond]; 
		Cell[CellGroupData[
			{Cell[BoxData[ToBoxes[cond]], "CondFulfilled", createCellMargin[66 + 27*level], CellDingbat -> StyleBox["\[CheckmarkedBox]", ShowStringCharacters -> False, StripOnInput -> False]], 
     		Cell[BoxData[ToBoxes[True]], "CondFulfilled", createCellMargin[66 + 27*level]]}
     	]]
     ]

condToCell[{cond_, calc__, True}, level_: 0] :=
	Module[{},
		Print["Second condlist ", cond]; 
		Cell[CellGroupData[
    		Join[
    			{Cell[BoxData[ToBoxes[cond]], "CondFulfilled", createCellMargin[66 + 27*level], CellDingbat -> StyleBox["\[CheckmarkedBox]", ShowStringCharacters -> False, StripOnInput -> False]]}, 
     			subcompToCell[#, level + 1] & /@ {calc},
     				{Cell[BoxData[ToBoxes[True]], "CondFulfilled", createCellMargin[66 + 27*level]]}
     		]
     	]]
     ]

createCellMargin[border_] := 
	CellMargins -> {{border, Inherited}, {Inherited, Inherited}}


(* already exists, make simpler *)

getStyle := 
	Module[{tmp, styles}, 
		tmp = NotebookOpen[FileNameJoin[{NotebookDirectory[], "Computation-Template.nb"}], Visible -> False];
		styles = NotebookGet[tmp];
		NotebookClose[tmp]; 
		styles /. Table[Apply[CMYKColor, IntegerDigits[i, 2, 4]] -> TMAcolor[i, "Milano"], {i, 0, 15}]
	]

TMAcolor[0, "Milano"] = RGBColor[0.91, 0.90, 0.85];(*beige*)
TMAcolor[1, "Milano"] = RGBColor[0.29, 0.46, 0.60];(*strong blue*)
TMAcolor[2, "Milano"] = RGBColor[0.36, 0.54, 0.69];(*light blue grey*)
TMAcolor[3, "Milano"] = RGBColor[0.957, 0.96, 0.97];(*grey96*)
TMAcolor[4, "Milano"] = RGBColor[0.88, 0.88, 0.92];(*grey90*)
TMAcolor[5, "Milano"] = RGBColor[0.73, 0.74, 0.84];(*grey75*)
TMAcolor[6, "Milano"] = RGBColor[0.404, 0.43, 0.545];(*blue*)
TMAcolor[7, "Milano"] = RGBColor[0.486, 0.33, 0.32];(*brown*)
TMAcolor[8, "Milano"] = RGBColor[0.89, 0.80, 0.69];(*light brown*)
TMAcolor[9, "Milano"] = RGBColor[0.73, 0.65, 0.61];(*medium brown*)
TMAcolor[10, "Milano"] = RGBColor[0.55, 0.44, 0.42];(*choko*)
TMAcolor[11, "Milano"] = RGBColor[0.23, 0.25, 0.34];(*blue grey*)
TMAcolor[12, "Milano"] = RGBColor[0.25, 0.19, 0.20];(*dark brown*)
TMAcolor[13, "Milano"] = RGBColor[0.55, 0.55, 0.55];(*grey55*)
TMAcolor[14, "Milano"] = RGBColor[0.40, 0.40, 0.40];(*grey40*)
TMAcolor[15, "Milano"] = RGBColor[0.30, 0.30, 0.30];(*grey30*)

End[]

EndPackage[]