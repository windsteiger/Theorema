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
PRFSIT$[ g:FML$[ _, And$TM[ P_, Q_], lab_], k_List, af_, i_String, rest___Rule] :> 
	Module[ {left, right},
		left = makeFML[ formula -> P, label -> lab <> ".1"];
		right = makeFML[ formula -> Q, label -> lab <> ".2"];
		proveAll[ makePRFINFO[ name -> andGoal, used -> g, generated -> {left, right}, id -> i], 
			makePRFSIT[ goal -> left, kb -> k, facts -> af, rest], 
			makePRFSIT[ goal -> right, kb -> k, facts -> af, rest]]
	]

inferenceRule[ implGoalDirect] = 
PRFSIT$[ g:FML$[ _, Implies$TM[ P_, Q_], _], k_, af_, i_String, rest___Rule] :> 
	Module[ {left, right},
		left = makeFML[ formula -> P];
		right = makeFML[ formula -> Q];
		proveAll[ makePRFINFO[ name -> implGoalDirect, used -> g, generated -> {left, right}, id -> i], 
			makePRFSIT[ goal -> right, kb -> Prepend[ k, left], facts -> af, rest]]
	]

inferenceRule[ implGoalCP] = 
PRFSIT$[ g:FML$[ _, Implies$TM[ P_, Q_], _], k_, af_, i_String, rest___Rule] :> 
	Module[ {negLeft, negRight},
		negLeft = makeFML[ formula -> Not$TM[ P]];
		negRight = makeFML[ formula -> Not$TM[ Q]];
		proveAll[ makePRFINFO[ name -> implGoalCP, used -> g, generated -> {negRight, negLeft}, id -> i], 
			makePRFSIT[ goal -> negLeft, kb -> Prepend[ k, negRight], facts -> af, rest]]
	]


connectiveRules = {"connectives", andGoal, andKB, implGoalDirect, implGoalCP};
equalityRules = {"equality", eqGoal, eqKB};

registerRuleSet[ "Quantifier Rules", quantifierRules, {forallGoal, forallKB, existsGoal, existsKB}]
registerRuleSet[ "Basic Prover", basicProver, {quantifierRules, connectiveRules, equalityRules}]

End[]

EndPackage[]