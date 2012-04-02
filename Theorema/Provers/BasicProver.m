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

BeginPackage[ "BasicProver`"]

Needs[ "Theorema`Provers`"]
Needs[ "Theorema`Common`"]
Needs[ "Theorema`Language`"]

Begin["`Private`"]

inferenceRule[ andGoal] = 
PRFSIT$[ goal:FML$[ k_, And$TM[ P_, Q_], lab_], kb_, af_, rest___, "ID" -> id_] :> 
	Module[ { left, right},
		left = FML$[ k, P, "(left)"];
		right = FML$[ k, Q, "(right)"];
		proveAll[ makePRFINFO[ "andGoal", {goal}, {left, right}, id], makePRFSIT[ left, kb, af, rest], makePRFSIT[ right, kb, af, rest]]
	]


connectiveRules = {"connectives", andGoal, andKB, implGoalMP, implGoalCP};
equalityRules = {"equality", eqGoal, eqKB};

registerRuleSet[ "Quantifier Rules", quantifierRules, {forallGoal, forallKB, existsGoal, existsKB}]
registerRuleSet[ "Basic Prover", basicProver, {quantifierRules, connectiveRules, equalityRules}]

End[]

EndPackage[]