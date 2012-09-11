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

applyOnce[ rules_Hold, ps_PRFSIT$] := 
	Module[ {i = ps.id, allRules = getActiveRules[ rules, Flatten], newNodes},
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

trySeveral[ rules_Hold, ps_PRFSIT$] :=
    Module[ {i = ps.id},
        makeORNODE[ makePRFINFO[ name -> proofAlternatives, used -> {ps[[1]]}, generated -> {ps[[2]]}, id -> i],
        	{Apply[ makePRFSIT[ goal -> #1, kb -> #2, facts -> #3, Apply[ Sequence, Cases[ ps, HoldPattern[ _String -> _]]]]&, ps], 
        	Apply[ makePRFSIT[ goal -> #1, kb -> #2, facts -> #3, Apply[ Sequence, Cases[ ps, HoldPattern[ _String -> _]]]]&, ps]}
        	]
    ]
trySeveral[ args___] := unexpected[ trySeveral, {args}]

registerStrategy[ "Apply once", applyOnce]
registerStrategy[ "Try several", trySeveral]

End[]

EndPackage[]