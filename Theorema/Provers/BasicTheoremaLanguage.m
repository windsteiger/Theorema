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

BeginPackage[ "Theorema`Provers`BasicTheoremaLanguage`"]

Needs[ "Theorema`Provers`"]
Needs[ "Theorema`Common`"]
Needs[ "Theorema`Language`"]

Begin["`Private`"]


(* ::Section:: *)
(* Connectives *)

(* ::Subsection:: *)
(* NOT *)

inferenceRule[ notGoal] = 
PRFSIT$[ g:FML$[ _, Not$TM[ a_], lab_], k_List, af_, i_String, rest___Rule] :> 
	Module[ {opp},
		opp = makeFML[ formula -> a];
		makeANDNODE[ makePRFINFO[ name -> notGoal, used -> g, generated -> opp, id -> i], 
			makePRFSIT[ goal -> makeFML[ formula -> False, label -> "F"], kb -> Prepend[ k, opp], facts -> af, rest]
		]
	]

inferenceRule[ contradiction] = 
PRFSIT$[ g:FML$[ _, a_, lab_] /; !TrueQ[ !a] && FreeQ[ g, _META$], k_List, af_, i_String, rest___Rule] :> 
	Module[ {opp},
		opp = makeFML[ formula -> Not$TM[ a]];
		makeANDNODE[ makePRFINFO[ name -> contradiction, used -> g, generated -> opp, id -> i], 
			makePRFSIT[ goal -> makeFML[ formula -> False, label -> "F"], kb -> Prepend[ k, opp], facts -> af, rest]
		]
	]
	
(* ::Subsection:: *)
(* AND *)

inferenceRule[ andGoal] = 
PRFSIT$[ g:FML$[ _, And$TM[ c__], lab_] /; FreeQ[ g, _META$], k_List, af_, i_String, rest___Rule] :> 
	Module[ {conj},
		conj = MapIndexed[ makeFML[ formula -> #1, label -> lab <> "." <> ToString[ #2[[1]]]]&, {c}];
		makeANDNODE[ makePRFINFO[ name -> andGoal, used -> g, generated -> conj, id -> i], 
			Map[ makePRFSIT[ goal -> #, kb -> k, facts -> af, rest]&, conj]
		]
	]

inferenceRule[ andKB] = 
PRFSIT$[ g_, {pre___, k:FML$[ _, And$TM[ c__], lab_], post___}, af_, i_String, rest___Rule] :> 
	Module[ {conj},
		conj = MapIndexed[ makeFML[ formula -> #1, label -> lab <> "." <> ToString[ #2[[1]]]]&, {c}];
		makeANDNODE[ makePRFINFO[ name -> andKB, used -> k, generated -> conj, id -> i], 
			makePRFSIT[ goal -> g, kb -> Join[ {pre}, conj, {post}], facts -> af, rest]
		]
	]


(* ::Subsection:: *)
(* OR *)

inferenceRule[ orGoal] = 
PRFSIT$[ g:FML$[ _, Or$TM[ a__, b_], lab_], k_List, af_, i_String, rest___Rule] :> 
	Module[ {negAssum, newG},
		negAssum = MapIndexed[ makeFML[ formula -> Not$TM[#1], label -> lab <> "." <> ToString[ #2[[1]]]]&, {a}];
		newG = makeFML[ formula -> b];
		makeANDNODE[ makePRFINFO[ name -> orGoal, used -> g, generated -> Append[ negAssum, newG], id -> i], 
			makePRFSIT[ goal -> newG, kb -> Join[ negAssum, k], facts -> af, rest]
		]
	]

inferenceRule[ orKB] = 
PRFSIT$[ g_, {pre___, k:FML$[ _, Or$TM[ c__], lab_], post___}, af_, i_String, rest___Rule] :> 
	Module[ {caseAssum},
		caseAssum = MapIndexed[ makeFML[ formula -> #1, label -> lab <> "." <> ToString[ #2[[1]]]]&, {c}];
		makeANDNODE[ makePRFINFO[ name -> orKB, used -> k, generated -> caseAssum, id -> i], 
			Map[ makePRFSIT[ goal -> g, kb -> {#, pre, post}, facts -> af, rest]&, caseAssum]
		]
	]


(* ::Subsection:: *)
(* Implication *)

inferenceRule[ implGoalDirect] = 
PRFSIT$[ g:FML$[ _, Implies$TM[ P_, Q_], _], k_, af_, i_String, rest___Rule] :> 
	Module[ {left, right},
		left = makeFML[ formula -> P];
		right = makeFML[ formula -> Q];
		makeANDNODE[ makePRFINFO[ name -> implGoalDirect, used -> g, generated -> {left, right}, id -> i], 
			makePRFSIT[ goal -> right, kb -> Prepend[ k, left], facts -> af, rest]]
	]

inferenceRule[ implGoalCP] = 
PRFSIT$[ g:FML$[ _, Implies$TM[ P_, Q_], _], k_, af_, i_String, rest___Rule] :> 
	Module[ {negLeft, negRight},
		negLeft = makeFML[ formula -> Not$TM[ P]];
		negRight = makeFML[ formula -> Not$TM[ Q]];
		makeANDNODE[ makePRFINFO[ name -> implGoalCP, used -> g, generated -> {negRight, negLeft}, id -> i], 
			makePRFSIT[ goal -> negLeft, kb -> Prepend[ k, negRight], facts -> af, rest]]
	]

(* ::Subsection:: *)
(* Equivalence *)


connectiveRules = {"Connectives Rules", 
	{notGoal, True, True, 30},
	{andGoal, True, True, 5},
	{andKB, True, False, 5},
	{orGoal, True, True, 5},
	{orKB, True, True, 19},
	{implGoalDirect, True, True, 5},
	{implGoalCP, False, False, 10}
	};
equalityRules = {"Equality Rules", 
	{eqGoal, False, False, 20},
	{eqKB, True, True, 15}
	};

registerRuleSet[ "Quantifier Rules", quantifierRules, {
	{forallGoal, True, True, 10},
	{forallKB, True, True, 70},
	{existsGoal, True, True, 50},
	{existsKB, True, True, 11}
	}]
registerRuleSet[ "Basic Theorema Language Rules", basicTheoremaLanguageRules, {
	quantifierRules, 
	connectiveRules, 
	equalityRules,
	{contradiction, True, True, 100}
	}]

End[]

EndPackage[]