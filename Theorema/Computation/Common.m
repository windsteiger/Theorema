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
trackCondition[ {}, expr_] /; $traceUserDef :=
	Module[{},
		insertInTrace[ {HoldForm[ expr]}, $TmaCompInsertPos];
  		AppendTo[ $TmaCompInsertPos, 2];
  		True
  	]
trackCondition[ {}, expr_] := True

trackCondition[ {x__}, expr_] /; $traceUserDef := 
	Module[{c, i, cond}, 
		cond = Hold[ x];
		insertInTrace[ {HoldForm[ expr]}, $TmaCompInsertPos];
		AppendTo[ $TmaCompInsertPos, 2]; 
  		insertInTrace[ {}, $TmaCompInsertPos]; 
  		AppendTo[ $TmaCompInsertPos, 1];
  		For[i = 1, i <= Length[ cond], i++,
   			insertInTrace[ {}, $TmaCompInsertPos]; 
   			AppendTo[ $TmaCompInsertPos, 1];
   			c = cond[[i]];
   			$TmaCompInsertPos = Most[ $TmaCompInsertPos];
   			If[ c === False,(* the current condition is not fulfilled *)
    			insertInTrace[ Extract[ cond, {i}, HoldForm], Append[ $TmaCompInsertPos, 1]];
    			insertInTrace[ False, Append[ $TmaCompInsertPos, Length[ Extract[ $TmaComputationObject, $TmaCompInsertPos]] + 1]];
    			$TmaCompInsertPos = Drop[ $TmaCompInsertPos, -2]; 
    			$TmaCompInsertPos = MapAt[ (# + 1)&, $TmaCompInsertPos, -1];
    			Return[ False]
    		];
   			If[ Not[ TrueQ[c]],(* the current condition couldn't be checked if it is true or false *)
    			insertInTrace[ Extract[ cond, {i}, HoldForm], Append[ $TmaCompInsertPos, 1]];
    			insertInTrace[ Indeterminate, Append[ $TmaCompInsertPos, Length[ Extract[ $TmaComputationObject, $TmaCompInsertPos]] + 1]];
    			$TmaCompInsertPos = Drop[ $TmaCompInsertPos, -2]; 
    			$TmaCompInsertPos = MapAt[ (# + 1)&, $TmaCompInsertPos, -1];
    			Return[ False]
    		];
   			(* the current condition is fulfilled *)
   			insertInTrace[ Extract[ cond, {i}, HoldForm], Append[ $TmaCompInsertPos, 1]];
   			insertInTrace[ True, Append[ $TmaCompInsertPos, Length[ Extract[ $TmaComputationObject, $TmaCompInsertPos]] + 1]];
   			$TmaCompInsertPos = ReplacePart[ $TmaCompInsertPos, -1 -> i + 1];
   		];
  		$TmaCompInsertPos = Most[ $TmaCompInsertPos]; 
   		$TmaCompInsertPos = MapAt[ (# + 1)&, $TmaCompInsertPos, -1];
   		Return[ True]
   	]

trackCondition[ {x__}, expr_] := And[ x]
trackCondition[ args___] := unexpected[ trackCondition, {args}]

(* Later maybe check condition with theorema prover *)
provecond[ cond_] := ReleaseHold[ cond]
provecond[ args___] := unexpected[ provecond, {args}]

insertInTrace[ toInsert_, pos_] := 
 	Module[{},
 		$TmaComputationObject = Insert[ $TmaComputationObject, toInsert, pos]
 	]
insertInTrace[ args___] := unexpected[ insertInTrace, {args}]

SetAttributes[ trackResult, HoldAll]
trackResult[ body_, form_FML$] /; $traceUserDef := 
 	Module[{v}, 
 		insertInTrace[ {{form, HoldForm[ body]}}, $TmaCompInsertPos]; 
  		$TmaCompInsertPos = AppendTo[ $TmaCompInsertPos, 2]; 
  		v = body; 
  		insertInTrace[ v, $TmaCompInsertPos]; 
  		$TmaCompInsertPos = Drop[ $TmaCompInsertPos, -2]; 
  		$TmaCompInsertPos = MapAt[ (# + 1)&, $TmaCompInsertPos, -1];
  		Return[v]
  	]
trackResult[ body_, form_FML$] := body
trackResult[ args___] := unexpected[ trackResult, {args}]

displayComputation[ file_String] := 
 	Module[{cells, calc = Get[ file]}, 
 		cells = {Cell[ CellGroupData[
 			Join[
 				(* The first element in the computation object is the box form of the input cell, we write it into the computation notebook as it is.*)
 				{Cell[ BoxData[ First[ calc]], "ComputationInput", CellMargins -> {{Inherited, Inherited}, {Inherited, 20}}]}, 
       			Map[ subcompToCell, Take[ calc, {2, -2}]],
       			{Cell[ BoxData[ theoremaBoxes[ Last[ calc]]], "ComputationOutput"]}
       		]]]};
       	$TmaComputationObject = calc;
       	$TmaComputationNotebook = tmaNotebookPut[ Notebook[ cells], "Computation"]
  	]
displayComputation[ args___] := unexpected[ displayComputation, {args}]

subcompToCell[ {def_, {{form_FML$, held_HoldForm}, res_}}, level_:0] := 
 	Module[{},
 		Cell[ CellGroupData[{
 			Cell[ BoxData[ theoremaBoxes[ def]], "Subfct", createCellMargin[27 + 27*level]], 
     		Cell[ CellGroupData[{
     			Cell[ BoxData[ theoremaBoxes[ held]], "Subfct", createCellMargin[27 + 27*level], CellFrameLabels -> {{formulaLabelRef[ form], ""}, {"", ""}}], 
        		Cell[ BoxData[ theoremaBoxes[ res]], "SubfctResult", createCellMargin[27 + 27*level]]}]
        	]}]
        ]
	]

subcompToCell[ {held_, {calc__}}, level_:0] := 
	Module[{},
  		Cell[ CellGroupData[{
  			Cell[ BoxData[ theoremaBoxes[ held]], "Subfct", createCellMargin[27 + 27*level]], 
  			subcompToCell[ {calc}, level + 1]}]
  		]
  	]

subcompToCell[ {{def_FML$, held_HoldForm}, res_}, level_:0] := 
	Module[{},
  		Cell[ CellGroupData[{
  			Cell[ BoxData[ theoremaBoxes[ held]], "Subfct", createCellMargin[27 + 27*level], CellFrameLabels -> {{formulaLabelRef[ def], ""}, {"", ""}}], 
     		Cell[ BoxData[ theoremaBoxes[ res]], "SubfctResult", createCellMargin[27 + 27*level]]}]
     	]
     ]

subcompToCell[ {def_, condlist:{{__, True|False|Indeterminate}..}}, level_:0] := 
	Module[{}, 
  		Cell[ CellGroupData[{
  			Cell[ BoxData[ theoremaBoxes[ def]], "Subfct", createCellMargin[27 + 27*level]], 
     		Cell[ CellGroupData[
     			Join[
     				{Cell[ "", "DummyHeaderFail", createCellMargin[66 + 27*level]]},
        			Map[ condToCell[ #, level, Closed]&, Drop[ condlist, -1]],
        			{condToCell[ condlist[[-1]]]}
        		]
        	]]}]
        ]
	]

subcompToCell[ {def_, condlist:{{__, True|False|Indeterminate}..}, res_}, level_:0] := 
	Module[{},
  		Cell[ CellGroupData[{
  			Cell[ BoxData[ theoremaBoxes[ def]], "Subfct", createCellMargin[27 + 27*level]], 
     		Cell[ CellGroupData[ 
     			Join[
     				{Cell[ "", "DummyHeaderOK", createCellMargin[66 + 27*level]]},
     				Map[ condToCell[ #, level]&, condlist]
     			]]], 
     		Cell[ CellGroupData[ {subcompToCell[ res, level+1]}]]}
     	]] 
	]
	
subcompToCell[ {{def_FML$, inp_HoldForm}, subcomp__, outp_}, level_:0] := 
	Module[{},
  		Cell[ CellGroupData[
    		Join[
    			{Cell[ BoxData[ theoremaBoxes[ inp]], "Subfct", createCellMargin[27 + 27*level], CellFrameLabels -> {{formulaLabelRef[ def], ""}, {"", ""}}]}, 
     			Map[ subcompToCell[ #, level + 1]&, {subcomp}],
     			{Cell[ BoxData[ theoremaBoxes[ outp]], "SubfctResult", createCellMargin[27 + 27*level]]}
     		]]
     	]
	]

subcompToCell[ args___] := unexpected[ subcompToCell, {args}]

condToCell[ {cond_, Indeterminate}, level_:0] := 
 	Module[{},
  		Cell[ BoxData[ theoremaBoxes[ cond]], "CondUndecided", createCellMargin[66 + 27*level]]
    ]

condToCell[ {cond_, calc__, Indeterminate}, level_:0] := 
 	Module[{},
  		Cell[ CellGroupData[
  			Join[
  				{Cell[ BoxData[ theoremaBoxes[ cond]], "CondUndecided", createCellMargin[66 + 27*level]]}, 
     			Map[ subcompToCell[ #, level+1]&, {calc}]
     		]]
     	]
     ]

condToCell[ {cond_, False}, level_:0] := 
	Module[{},
		Cell[ CellGroupData[{
			Cell[ BoxData[ theoremaBoxes[ cond]], "CondNotFulfilled", createCellMargin[66 + 27*level]], 
     		Cell[ BoxData[ ToBoxes[ False]], "CondNotFulfilled", createCellMargin[66 + 27*level],
     			CellDingbat -> None]}]
     	]
     ]

condToCell[ {cond_, calc__, False}, level_:0] := 
	Module[{},
  		Cell[ CellGroupData[
    		Join[
    			{Cell[ BoxData[ theoremaBoxes[ cond]], "CondNotFulfilled", createCellMargin[66 + 27*level]]}, 
     			Map[ subcompToCell[ #, level+1]&, {calc}],
     			{Cell[ BoxData[ ToBoxes[ False]], "CondNotFulfilled", createCellMargin[66 + 27*level],
     				CellDingbat -> None]}
     		]]
     	]
     ]

condToCell[ {cond_, True}, level_:0, status_:Open] := 
	Module[{},
		Cell[ CellGroupData[{
			Cell[ BoxData[ theoremaBoxes[ cond]], "CondFulfilled", createCellMargin[66 + 27*level]], 
     		Cell[ BoxData[ ToBoxes[ True]], "CondFulfilled", createCellMargin[66 + 27*level],
     			CellDingbat -> None]},
     		status]
     	]
    ]

condToCell[ {cond_, calc__, True}, level_:0, status_:Open] :=
	Module[{},
		Cell[ CellGroupData[
    		Join[
    			{Cell[ BoxData[ theoremaBoxes[ cond]], "CondFulfilled", createCellMargin[66 + 27*level]]}, 
     			Map[ subcompToCell[ #, level+1]&, {calc}],
     			{Cell[ BoxData[ ToBoxes[ True]], "CondFulfilled", createCellMargin[66 + 27*level],
     				CellDingbat -> None]}
     		],
     		status]
     	]
    ]
condToCell[ args___] := unexpected[ condToCell, {args}]

createCellMargin[ border_] := CellMargins -> {{border, Inherited}, {1, 1}}
createCellMargin[ args___] := unexpected[ createCellMargin, {args}]

formulaLabelRef[ f_FML$] :=
	Module[{lab, fmlDisp = theoremaDisplay[ formula@f]},
		lab = makeLabel[ label@f];
		With[ {file = sourceFile@f, tag = id@f},
			Cell[ BoxData[ ToBoxes[
            	Button[ Tooltip[ Mouseover[ Style[ lab, "FormReference"], Style[ lab, "FormReferenceHover"]], fmlDisp],
               		NotebookLocate[ {file, tag}], Appearance -> None]
        	]]]
		]
	]
formulaLabelRef[ args___] := unexpected[ formulaLabelRef, {args}]



End[]
EndPackage[]