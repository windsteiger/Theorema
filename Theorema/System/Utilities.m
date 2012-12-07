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

BeginPackage["Theorema`System`Utilities`"]

Needs["Theorema`Common`"]

Begin["`Private`"]


(* ::Subsubsection:: *)
(* unexpected *)

unexpected[f_, args_List] := 
	Module[{}, 
		Message[ Theorema::unexpectedArgs, f, args];
		Throw[f]
	]

(* ::Subsubsection:: *)
(* replaceAllExcept *)

Options[replaceAllExcept] = {Heads -> {}};

replaceAllExcept[expr_, rules_List, expt_List, opts___?OptionQ] :=
  	Module[{exptRules, heads},
  		{heads} = {Heads} /. {opts} /. Options[replaceAllExcept];
   		exptRules = Join[ Map[(# -> #) &, expt], rules, Map[(HoldPattern[#[x___]] :> #[x]) &, heads]];
   		expr /. exptRules];

replaceAllExcept[expr_, r_?(MemberQ[{Rule, RuleDelayed}, Head[#]]&), expt_List, opts___?OptionQ] := replaceAllExcept[expr, {r}, expt, opts];
replaceAllExcept[args___] := unexpected[ replaceAllExcept, {args}]


(* ::Subsubsection:: *)
(* applyHold *)

applyHold[Hold[a_], Hold[b___]] := Hold[a[b]];

(* ::Subsubsection:: *)
(* joinHold *)

joinHold[Hold[a___], Hold[b___]] := Hold[a, b];

(* ::Subsubsection:: *)
(* notification *)

notification[msg__] /; $Notebooks := MessageDialog[ StringForm[msg]]
notification[msg__] := Message[ StringForm[msg]]
notification[args___] := unexpected[notification, {args}]

End[]

EndPackage[]