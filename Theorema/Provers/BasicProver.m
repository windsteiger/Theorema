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

BeginPackage[ "Theorema`Provers`BasicProver`"]

Needs[ "Theorema`Provers`"]
Needs[ "Theorema`Common`"]
Needs[ "Theorema`Language`"]

Begin["`Private`"]

inferenceRule[ andGoal] = 
PRFSIT$[ goal:FML$[ k_, And$TM[ P_, Q_], lab_], kb_, af_, rest___, "ID" -> id_] :> 
	Module[ { left, right},
		left = makeFML[ formula -> P, label -> lab <> ".1"];
		right = makeFML[ formula -> Q, label -> lab <> ".2"];
		proveAll[ makePRFINFO[ "andGoal", {goal}, {left, right}, id], makePRFSIT[ left, kb, af, rest], makePRFSIT[ right, kb, af, rest]]
	]

inferenceRule[ implGoalDirect] = 
PRFSIT$[ goal:FML$[ k_, Implies$TM[ P_, Q_], lab_], kb_, af_, rest___, "ID" -> id_] :> 
	Module[ { left, right},
		left = makeFML[ formula -> P];
		right = makeFML[ formula -> Q];
		proveAll[ makePRFINFO[ "implGoalDirect", {goal}, {left, right}, id], makePRFSIT[ right, Prepend[ kb, left], af, rest]]
	]

inferenceRule[ implGoalCP] = 
PRFSIT$[ goal:FML$[ k_, Implies$TM[ P_, Q_], lab_], kb_, af_, rest___, "ID" -> id_] :> 
	Module[ { negLeft, negRight},
		negLeft = makeFML[ formula -> Not$TM[ P]];
		negRight = makeFML[ formula -> Not$TM[ Q]];
		proveAll[ makePRFINFO[ "implGoalCP", {goal}, {negLeft, negRight}, id], makePRFSIT[ negLeft, Prepend[ kb, negRight], af, rest]]
	]


connectiveRules = {"connectives", andGoal, andKB, implGoalDirect, implGoalCP};
equalityRules = {"equality", eqGoal, eqKB};

registerRuleSet[ "Quantifier Rules", quantifierRules, {forallGoal, forallKB, existsGoal, existsKB}]
registerRuleSet[ "Basic Prover", basicProver, {quantifierRules, connectiveRules, equalityRules}]

End[]

EndPackage[]