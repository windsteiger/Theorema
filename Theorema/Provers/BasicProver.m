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

BeginPackage["BasicProver`"]

Needs[ "Theorema`Provers`"]
Needs[ "Theorema`Common`"]
Needs[ "Theorema`Language`"]

Begin["`Private`"]

inferenceRule[ andGoal] = 
_[ goal:{k_, And$TM[ P_, Q_], lab_}, kb_, af_, rest___, "ID" -> id_] :> 
	Module[ { left, right},
		left = {k, P, "(left)"};
		right = {k, Q, "(right)"};
		proveAll[ makePRFINFO[ "andGoal", {goal}, {left, right}, id], makePRFSIT[ left, kb, af, rest], makePRFSIT[ right, kb, af, rest]]
	]


connectiveRules = {"connectives", andGoal, andKB, implGoalMP, implGoalCP};
equalityRules = {"equality", eqGoal, eqKB};

registerRuleSet[ "Quantifier Rules", quantifierRules, {forallGoal, forallKB, existsGoal, existsKB}]
registerRuleSet[ "Basic Prover", basicProver, {quantifierRules, connectiveRules, equalityRules}]

applyOnce[ rules_, ps_] := 
	Module[ {id = getNodeID[ ps], ruleSyms = getActiveRules[ rules, Flatten], allRules, newPSits},
		allRules = DeleteCases[ Map[ inferenceRule, ruleSyms], _inferenceRule];
		newPSits = ReplaceList[ ps, allRules];
		Switch[ Length[ newPSits],
			0,
			proofFails[ makePRFINFO[ "noApplicableRule", {}, {}, id]],
			1,
			First[ newPSits],
			_,
			proveSome[ 
				makePRFINFO[ "ProofAlternatives", Apply[ Union, Map[ getUsed, newPSits]], Apply[ Union, Map[ getGenerated, newPSits]], id],
				Apply[ Sequence, newPSits]]
		]
	]
applyOnce[ args___] := unexpected[ applyOnce, {args}]

trySeveral[ rules_, ps_] :=
    Module[ {id = getNodeID[ ps]},
        proveSome[ makePRFINFO[ "ProofAlternatives", {ps[[1]]}, {ps[[2]]}, id],
        	Apply[ makePRFSIT, Drop[ ps, -1]], Apply[ makePRFSIT, Drop[ ps, -1]]]
    ]
trySeveral[ args___] := unexpected[ trySeveral, {args}]

registerStrategy[ "Apply once", applyOnce]
registerStrategy[ "Try several", trySeveral]

End[]

EndPackage[]