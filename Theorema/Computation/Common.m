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

SetAttributes[ trackCondition, HoldAll]
SetAttributes[ trackResult, HoldAll]

trackCondition[ {}, fct_, param_] :=
	Module[{},
		insertInTrace[$TmaComputationObject, {Apply[HoldForm[fct], param]}, $TmaCompInsertPos];
  		AppendTo[$TmaCompInsertPos, 2];
  		True
  	]

trackCondition[ {x__}, fct_, param_] := 
	Module[{c, i, cond}, 
		cond = Hold[ x];
		insertInTrace[$TmaComputationObject, {Apply[HoldForm[fct], param]}, $TmaCompInsertPos];
		AppendTo[$TmaCompInsertPos, 2]; 
  		insertInTrace[$TmaComputationObject, {}, $TmaCompInsertPos]; 
  		AppendTo[$TmaCompInsertPos, 1];
  		For[i = 1, i <= Length[cond], i++,
   			insertInTrace[$TmaComputationObject, {}, $TmaCompInsertPos]; 
   			AppendTo[$TmaCompInsertPos, 1];
   			c = cond[[i]];
   			$TmaCompInsertPos = Most[$TmaCompInsertPos];
   			If[c === False,(* the current condition is not fulfilled *)
    			insertInTrace[$TmaComputationObject, Extract[ cond, {i}, HoldForm], Append[$TmaCompInsertPos, 1]];
    			insertInTrace[$TmaComputationObject, False, Append[$TmaCompInsertPos, Length[Extract[$TmaComputationObject, $TmaCompInsertPos]] + 1]];
    			$TmaCompInsertPos = Most[$TmaCompInsertPos]; 
    			insertInTrace[$TmaComputationObject, {False, i}, $TmaCompInsertPos]; 
    			$TmaCompInsertPos = Most[$TmaCompInsertPos]; 
    			$TmaCompInsertPos[[Length[$TmaCompInsertPos]]] = $TmaCompInsertPos[[Length[$TmaCompInsertPos]]] + 1;
    			Return[False]
    		];
   			If[Not[TrueQ[c]],(* the current condition couldn't be checked if it is true or false *)
    			insertInTrace[$TmaComputationObject, Extract[ cond, {i}, HoldForm], Append[$TmaCompInsertPos, 1]];
    			insertInTrace[$TmaComputationObject, "undetermined", Append[$TmaCompInsertPos, Length[Extract[$TmaComputationObject, $TmaCompInsertPos]] + 1]];
    			$TmaCompInsertPos = Most[$TmaCompInsertPos]; 
    			insertInTrace[$TmaComputationObject, {"undetermined", i}, $TmaCompInsertPos]; 
    			$TmaCompInsertPos = Most[$TmaCompInsertPos]; 
    			$TmaCompInsertPos[[Length[$TmaCompInsertPos]]] = $TmaCompInsertPos[[Length[$TmaCompInsertPos]]] + 1;
    			Return[False]
    		];
   			(* the current condition is fulfilled *)
   			insertInTrace[$TmaComputationObject, Extract[ cond, {i}, HoldForm], Append[$TmaCompInsertPos, 1]];
   			insertInTrace[$TmaComputationObject, True, Append[$TmaCompInsertPos, Length[Extract[$TmaComputationObject, $TmaCompInsertPos]] + 1]];
   			$TmaCompInsertPos[[Length[$TmaCompInsertPos]]] = i + 1;
   		];
  		$TmaCompInsertPos = Most[$TmaCompInsertPos]; 
  		insertInTrace[$TmaComputationObject, {True, 0}, $TmaCompInsertPos];
   		$TmaCompInsertPos[[Length[$TmaCompInsertPos]]] = $TmaCompInsertPos[[Length[$TmaCompInsertPos]]] + 2;
   		Return[True]
   	]
trackCondition[ args___] := unexpected[ trackCondition, {args}]

provecond[cond_] := 
 	Module[{}, 
  		Return[ReleaseHold[cond]](*check condition with theorema proofer *)
  	]

SetAttributes[ insertInTrace, HoldFirst];
insertInTrace[ calc_, toInsert_, pos_] := 
 	Module[{},
 		calc = Insert[ calc, toInsert, pos]
 	]

trackResult[body_] := 
 	Module[{v}, 
 		insertInTrace[$TmaComputationObject, {HoldForm[body]}, $TmaCompInsertPos]; 
  		$TmaCompInsertPos = AppendTo[$TmaCompInsertPos, 2]; v = body; 
  		insertInTrace[$TmaComputationObject, v, $TmaCompInsertPos]; 
  		$TmaCompInsertPos = Most[Most[$TmaCompInsertPos]]; 
  		$TmaCompInsertPos[[Length[$TmaCompInsertPos]]] = $TmaCompInsertPos[[Length[$TmaCompInsertPos]]] + 1;
  		Return[v]
  	]

displayComputation[calclist_] := 
 	Module[{cells}, 
 		cells = {Cell[CellGroupData[
 			Join[{Cell[BoxData[ToBoxes[First[calclist]]], "CalculationInput"]}, 
       			Map[subcompToCell, Drop[Drop[calclist, 1], -1]],
       			{Cell[BoxData[ToBoxes[Last[calclist]]], "CalculationInput"]}
       			]]]};
       	$TmaComputationNotebook = tmaNotebookPut[ Notebook[ cells], "Computation"]
  		]

subcompToCell[{inp_, subcomp__, outp_}, level_: 0] := 
	Module[{},
		Print[level, " Subcomputation detected"];
		Print[subcomp]; 
  		Cell[CellGroupData[
    		Join[{Cell[BoxData[ToBoxes[inp]], "Subfct", createCellMargin[27 + 27*level]]}, 
     			subcompToCell[#, level + 1] & /@ {subcomp},
     				{Cell[BoxData[ToBoxes[outp]], "Subfct_result", createCellMargin[27 + 27*level]]}
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
        		Cell[BoxData[ToBoxes[res]], "Subfct_result", createCellMargin[27 + 27*level]]}
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
     		Cell[BoxData[ToBoxes[res]], "Subfct_result", createCellMargin[27 + 27*level]]}
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
        			condToCell[#, level, Closed] & /@ condlist[[1 ;; n - 1]],
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
        			condToCell[#, level, Closed] & /@ condlist[[1 ;; n - 1]], 
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

condToCell[{cond_, True}, level_: 0, status_: Open] := 
	Module[{},
		Print[cond]; 
		Cell[CellGroupData[
			{Cell[BoxData[ToBoxes[cond]], "CondFulfilled", createCellMargin[66 + 27*level], CellDingbat -> StyleBox["\[CheckmarkedBox]", ShowStringCharacters -> False, StripOnInput -> False]], 
     		Cell[BoxData[ToBoxes[True]], "CondFulfilled", createCellMargin[66 + 27*level]]},status
     	]]
     ]

condToCell[{cond_, calc__, True}, level_: 0, status_: Open] :=
	Module[{},
		Print["Second condlist ", cond]; 
		Cell[CellGroupData[
    		Join[
    			{Cell[BoxData[ToBoxes[cond]], "CondFulfilled", createCellMargin[66 + 27*level], CellDingbat -> StyleBox["\[CheckmarkedBox]", ShowStringCharacters -> False, StripOnInput -> False]]}, 
     			subcompToCell[#, level + 1] & /@ {calc},
     				{Cell[BoxData[ToBoxes[True]], "CondFulfilled", createCellMargin[66 + 27*level]]}
     		],status
     	]]
     ]

createCellMargin[border_] := 
	CellMargins -> {{border, Inherited}, {Inherited, Inherited}}

End[]

EndPackage[]