(* Theorema 
    Copyright (C) 2010 The Theorema Group

    This file is part of Theorema 2.0
    
    Theorema 2.0 is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Theorema 2.0 is distributed in the hope that it will be useful,
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
	Module[ {allRules = getActiveRulesFilter[ ps, "term", Flatten], newNodes},
		newNodes = applyAllRules[ ps, allRules];
		Switch[ Length[ newNodes],
			0,
			makeTERMINALNODE[ makePRFINFO[ name -> noApplicableRule, used -> Prepend[ kb@ps, goal@ps], "openPS" -> Drop[ Apply[ List, ps], 2]], failed],
			1,
			First[ newNodes],
			_,
			makeORNODE[ 
				makePRFINFO[ name -> proofAlternatives, used -> used@newNodes, generated -> generated@newNodes],
				newNodes]
		]
	]
applyOnce[ args___] := unexpected[ applyOnce, {args}]

applyOnceAndLevelSaturation[ ps_PRFSIT$] :=
	Module[ {satps = ps, allRules = getActiveRulesFilter[ ps, "term"|"levelSat1"|"levelSat2", Flatten], 
		sat1 = getActiveRulesType[ ps, "levelSat1"], 
		sat2 = getActiveRulesType[ ps, "levelSat2"], newNodes, reSat},
		If[ id@ps === "InitialPS",
			satps = levelSaturation[ ps, sat1, sat2];
			If[ isProofNode[ satps],
				Return[ satps]
			]			
		];
		newNodes = applyAllRules[ satps, allRules];
		If[ newNodes === {},
			(* no rule applied *)
			reSat = levelSaturation[ satps, sat1, sat2];
			If[ !MatchQ[ reSat, _PRFSIT$],
				(* levelSaturation generated new formulae and returned an ANDNODE *)
				newNodes = {reSat}
				(* otherwise, levelSaturation returned a PRFSIT and we do nothing, i.e. newNodes stays {} *)
			],
			(* at least one proof rule applied, and we saturate all pending PRFSITs *)
			newNodes = MapAt[ levelSaturation[ #, sat1, sat2]&, newNodes, Position[ newNodes, _PRFSIT$]]
		];
		Switch[ Length[ newNodes],
			0,
			makeTERMINALNODE[ makePRFINFO[ name -> noApplicableRule, used -> Prepend[ kb@ps, goal@ps], "openPS" -> Drop[ Apply[ List, ps], 2]], failed],
			1,
			First[ newNodes],
			_,
			makeORNODE[ 
				makePRFINFO[ name -> proofAlternatives, used -> used@newNodes, generated -> generated@newNodes],
				newNodes]
		]
	]
applyOnceAndLevelSaturation[ args___] := unexpected[ applyOnceAndLevelSaturation, {args}]

(* ::Section:: *)
(* Level saturation *)

levelSaturation[ ps:PRFSIT$[ _, k_, _, rest___?OptionQ], sat1rules_List, sat2rules_List] :=
	Module[{satKB, psKB = k, l, posNew, posRearrKB, pairs = {}, i, j,
			newForms, newPairs, newFrom1, newFrom2, usd={}, gen={}, nextGen},
		l = Length[ k];
		satKB = getOptionalComponent[ ps, "lastSat"];
		(* list of positions of new forms in KB since last saturation run
		   Since KB is a plain unstructured list all positions are specified by exactly 1 integer *)
		posNew = Position[ k, _?(!MemberQ[ satKB, key[#]]&), {1}, Heads -> False];
		(* we build a list with pos of new forms followed by pos of the remaining (old) forms *)
		posRearrKB = Join[ posNew, Complement[ Map[ List, Range[ l]], posNew]];
		(* we form a list of new forms and a list of pairs involving the new forms just based on the positions *)
		Do[
			Do[ 
				AppendTo[ pairs, {posRearrKB[[j]], posRearrKB[[i]]}],
				{i, j+1, l}], 
			{j, Length[ posNew]}];
		newForms = Extract[ k, posNew];
		(* We do not check success and generate rewrite rules when applying the individual rules.
			This will happen below when we use joinKB and toBeProved anyway. *)
		Block[{$TMAcheckSuccess = False, $autoGenerateRules = False},
			newFrom1 = Map[ applyAllRules[ #, sat1rules]&, Map[ dummyGoalPS[ #, rest]&, newForms]];
			newPairs = Map[ Extract[ k, #]&, pairs];
			newFrom2 = Map[ applyAllRules[ #, sat2rules]&, Map[ dummyGoalPS[ #, rest]&, newPairs]];
		];
		Block[ {$rewriteRules = {}},
		(* Go through the new proof sits generated from one formula and extract the necessary info *)
			Do[
				nextGen = extractGenerated[ newFrom1[[j]]];
				If[ nextGen =!= {},
					(* if some new forms have been generated: we keep track *)
					(* which forms were used ... *)
					AppendTo[ usd, {newForms[[j]]}];
					(* which forms were generated ... *)
					AppendTo[ gen, nextGen];
					(* and join the new forms to the kb *)
					psKB = joinKB[ nextGen, psKB]
				],
				{j, Length[ newFrom1]}
			];
		(* Go through the new proof sits generated from two formulas and extract the necessary info *)
			Do[
				nextGen = extractGenerated[ newFrom2[[j]]];
				If[ nextGen =!= {},
					(* if some new forms have been generated: we keep track *)
					(* which forms were used ... *)
					AppendTo[ usd, newPairs[[j]]];
					(* which forms were generated ... *)
					AppendTo[ gen, nextGen];
					(* and join the new forms to the kb *)
					psKB = joinKB[ nextGen, psKB]
				],
				{j, Length[ newFrom2]}
			];
			If[ gen === {},
				(* In this case, 'rest' already has the right rewrite rules. No new ones need to be joined *)
				makePRFSIT[ goal -> goal@ps, kb -> psKB, id -> id@ps, "lastSat" -> Map[ key, k], rest],
				(* else: In this case we must join the rules collected above to the ones that were aleady there *)
				makeANDNODE[ makePRFINFO[ name -> levelSat, used -> usd, generated -> gen], 
                	toBeProved[ goal -> goal@ps, kb -> psKB, "lastSat" -> Map[ key, k], rest]]
			]
		]
	]
levelSaturation[ args___] := unexpected[ levelSaturation, {args}]

(* In level sat above, dummyGoalPS is called inside a Block[{$autoGenerateRules = False},...] anyway. We put the block here as well in case
	we want to use the function somewhere else in future. *)
dummyGoalPS[ f_FML$, rest___] := Block[ {$autoGenerateRules = False},
	makePRFSIT[ kb -> {f}, id -> "dummy", rest]
]
dummyGoalPS[ pair:{_FML$, _FML$}, rest___] := Block[ {$autoGenerateRules = False},
	makePRFSIT[ kb -> pair, id -> "dummy", rest]
]
dummyGoalPS[ args___] := unexpected[ dummyGoalPS, {args}]

extractGenerated[ nodes_List] := Union[ Flatten[ Map[ generated, nodes]], SameTest -> (formula[#1] === formula[#2]&)]
extractGenerated[ args___] := unexpected[ extractGenerated, {args}]


(*
	This is not serious, it just duplicates the proof situation into two children. Should be a test case for exhaustive search
	until search depth is reached.
*)
trySeveral[ ps_PRFSIT$] :=
    Module[ {},
        makeORNODE[ makePRFINFO[ name -> proofAlternatives, used -> {goal@ps}, generated -> {kb@ps}, id -> id@ps],
        	{Apply[ toBeProved[ goal -> #1, kb -> #2, #4, #5, #6, #7, #8,
        		Apply[ Sequence, Cases[ ps, HoldPattern[ (Rule|RuleDelayed)[_String, _]]]]]&, ps], 
        	Apply[ toBeProved[ goal -> #1, kb -> #2, #4, #5, #6, #7, #8,
        		Apply[ Sequence, Cases[ ps, HoldPattern[ (Rule|RuleDelayed)[_String, _]]]]]&, ps]}
        	]
    ]
trySeveral[ args___] := unexpected[ trySeveral, {args}]

registerStrategy[ "Apply once", applyOnce]
registerStrategy[ "Apply once + Level saturation", applyOnceAndLevelSaturation]
(*
registerStrategy[ "Try several", trySeveral]
*)

End[]

EndPackage[]