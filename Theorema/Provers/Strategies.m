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

applyOnce[ rules_, ps_] := 
	Module[ {i = getNodeID[ ps], ruleSyms = getActiveRules[ rules, Flatten], allRules, newPSits},
		allRules = DeleteCases[ Map[ inferenceRule, ruleSyms], _inferenceRule];
		newPSits = ReplaceList[ ps, allRules];
		Switch[ Length[ newPSits],
			0,
			proofFails[ makePRFINFO[ name -> noApplicableRule, id -> i]],
			1,
			First[ newPSits],
			_,
			newPSits = Map[ renewID, newPSits];
			proveSome[ 
				makePRFINFO[ name -> proofAlternatives, used -> Apply[ Union, Map[ getUsed, newPSits]], generated -> Apply[ Union, Map[ getGenerated, newPSits]], id -> i],
				Apply[ Sequence, newPSits]]
		]
	]
applyOnce[ args___] := unexpected[ applyOnce, {args}]

trySeveral[ rules_, ps_] :=
    Module[ {i = getNodeID[ ps]},
        proveSome[ makePRFINFO[ name -> proofAlternatives, used -> {ps[[1]]}, generated -> {ps[[2]]}, id -> i],
        	Apply[ makePRFSIT[ goal -> #1, kb -> #2, facts -> #3, Apply[ Sequence, Cases[ ps, HoldPattern[ _String -> _]]]]&, ps], 
        	Apply[ makePRFSIT[ goal -> #1, kb -> #2, facts -> #3, Apply[ Sequence, Cases[ ps, HoldPattern[ _String -> _]]]]&, ps]
        	]
    ]
trySeveral[ args___] := unexpected[ trySeveral, {args}]

registerStrategy[ "Apply once", applyOnce]
registerStrategy[ "Try several", trySeveral]

End[]

EndPackage[]