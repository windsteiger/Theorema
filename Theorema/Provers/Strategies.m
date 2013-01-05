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

BeginPackage["Theorema`Provers`Strategies`"]

Needs[ "Theorema`Common`"]
Needs[ "Theorema`Provers`"]

Begin["`Private`"]

(* ::Section:: *)
(* Proof strategies *)

applyOnce[ ps_PRFSIT$] := 
	Module[ {i = ps.id, allRules = getActiveRulesFilter[ ps, "term", Flatten], newNodes},
		newNodes = applyAllRules[ ps, allRules];
		Switch[ Length[ newNodes],
			0,
			proofFails[ makePRFINFO[ name -> noApplicableRule, id -> i]],
			1,
			First[ newNodes],
			_,
			newNodes = Map[ renewID, newNodes];
			makeORNODE[ 
				makePRFINFO[ name -> proofAlternatives, used -> newNodes.used, generated -> newNodes.generated, id -> i],
				newNodes]
		]
	]
applyOnce[ args___] := unexpected[ applyOnce, {args}]

applyOnceAndLevelSaturation[ ps_PRFSIT$] :=
	Module[ {i = ps.id, allRules = getActiveRulesFilter[ ps, "term"|"levelSat1"|"levelSat2", Flatten], 
		sat1 = getActiveRulesType[ ps, "levelSat1"], 
		sat2 = getActiveRulesType[ ps, "levelSat2"], newNodes},
		newNodes = applyAllRules[ ps, allRules];
		newNodes = MapAt[ levelSaturation[ #, sat1, sat2]&, newNodes, Position[ newNodes, _PRFSIT$]];
		Switch[ Length[ newNodes],
			0,
			proofFails[ makePRFINFO[ name -> noApplicableRule, id -> i]],
			1,
			First[ newNodes],
			_,
			newNodes = Map[ renewID, newNodes];
			makeORNODE[ 
				makePRFINFO[ name -> proofAlternatives, used -> newNodes.used, generated -> newNodes.generated, id -> i],
				newNodes]
		]
	]
applyOnceAndLevelSaturation[ args___] := unexpected[ applyOnceAndLevelSaturation, {args}]

levelSaturation[ ps:PRFSIT$[ _, _, _, _, rest___?OptionQ], sat1rules_List, sat2rules_List] :=
	Module[{locInfo = ps.local, satKB, psKB = ps.kb, l, posNew, posRearrKB, pairs = {}, i, j,
			newForms, newPairs, newFrom1, newFrom2, usd={}, gen={}, nextGen},
		l = Length[ psKB];
		satKB = getLocalInfo[ locInfo, "lastSat"];
		(* list of positions of new forms in KB since last saturation run
		   Since KB is a plain unstructured list all positions are specified by exactly 1 integer *)
		posNew = Position[ psKB, _?(!MemberQ[ satKB, #.id]&), {1}, Heads -> False];
		(* we build a list with pos of new forms followed by pos of the remaining (old) forms *)
		posRearrKB = Join[ posNew, Complement[ Map[ List, Range[ l]], posNew]];
		(* we form a list of new forms and a list of pairs involving the new forms just based on the positions *)
		Do[
			Do[ 
				AppendTo[ pairs, {posRearrKB[[j]], posRearrKB[[i]]}],
				{i, j+1, l}], 
			{j, Length[ posNew]}];
		newForms = Extract[ psKB, posNew];
		newFrom1 = Map[ applyAllRules[ #, sat1rules]&, Map[ dummyGoalPS[ #, rest]&, newForms]];
		newFrom1 = Map[ extractGenerated, newFrom1];
		newPairs = Map[ Extract[ psKB, #]&, pairs];
		newFrom2 = Map[ applyAllRules[ #, sat2rules]&, Map[ dummyGoalPS[ #, rest]&, newPairs]];
		newFrom2 = Map[ extractGenerated, newFrom2];
		locInfo = putLocalInfo[ locInfo, "lastSat" -> Map[ #.key&, psKB]];
		Do[
			nextGen = newFrom1[[j]];
			If[ nextGen =!= {},
				AppendTo[ usd, {newForms[[j]]}];
				AppendTo[ gen, nextGen];
				psKB = joinKB[ psKB, nextGen]
			],
			{j, Length[ newFrom1]}
		];
		Do[
			nextGen = newFrom2[[j]];
			If[ nextGen =!= {},
				AppendTo[ usd, newPairs[[j]]];
				AppendTo[ gen, nextGen];
				psKB = joinKB[ psKB, nextGen]
			],
			{j, Length[ newFrom2]}
		];
		makeANDNODE[ makePRFINFO[ name -> levelSat, used -> usd, generated -> gen, id -> ps.id], 
                newSubgoal[ goal -> ps.goal, kb -> psKB, local -> locInfo, rest]]
	]
levelSaturation[ args___] := unexpected[ levelSaturation, {args}]

dummyGoalPS[ f_FML$, rest___?OptionQ] := makePRFSIT[ goal -> f, kb -> {f}, id -> "dummy", rest]
dummyGoalPS[ pair:{f_FML$, _FML$}, rest___?OptionQ] := makePRFSIT[ goal -> f, kb -> pair, id -> "dummy", rest]
dummyGoalPS[ args___] := unexpected[ dummyGoalPS, {args}]

extractGenerated[ nodes_List] := Union[ Flatten[ Map[ #.generated&, nodes]], SameTest -> (#1.formula === #2.formula&)]
extractGenerated[ args___] := unexpected[ extractGenerated, {args}]

(*
	This is not serious, it just duplicates the proof situation into two children. Should be a test case for exhaustive search
	until search depth is reached.
*)
trySeveral[ ps_PRFSIT$] :=
    Module[ {},
        makeORNODE[ makePRFINFO[ name -> proofAlternatives, used -> {ps.goal}, generated -> {ps.kb}, id -> ps.id],
        	{Apply[ newSubgoal[ goal -> #1, kb -> #2, #4, #5, #6, #7, #8,
        		Apply[ Sequence, Cases[ ps, HoldPattern[ (Rule|RuleDelayed)[_String, _]]]]]&, ps], 
        	Apply[ newSubgoal[ goal -> #1, kb -> #2, #4, #5, #6, #7, #8,
        		Apply[ Sequence, Cases[ ps, HoldPattern[ (Rule|RuleDelayed)[_String, _]]]]]&, ps]}
        	]
    ]
trySeveral[ args___] := unexpected[ trySeveral, {args}]

registerStrategy[ "Apply once", applyOnce]
registerStrategy[ "Apply once + Level saturation", applyOnceAndLevelSaturation]
registerStrategy[ "Try several", trySeveral]

End[]

EndPackage[]