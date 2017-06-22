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

BeginPackage["Theorema`System`Utilities`"]

Needs["Theorema`Common`"]

Begin["`Private`"]


(* ::Subsubsection:: *)
(* unexpected *)

unexpected[f_, args_List] :=
    Module[ {},
        Message[ Theorema::unexpectedArgs, f, args];
        Throw[ f]
    ]

(* ::Subsubsection:: *)
(* replaceAllExcept *)

Options[replaceAllExcept] = {Heads -> {}};

replaceAllExcept[expr_, rules_List, expt_List, opts___?OptionQ] :=
  	Module[{exptRules, heads},
  		{heads} = {Heads} /. {opts} /. Options[replaceAllExcept];
   		exptRules = Join[ Map[(# -> #) &, expt], rules, Map[(HoldPattern[#[x___]] :> #[x]) &, heads]];
   		expr /. exptRules];

replaceAllExcept[expr_, r_Rule|r_RuleDelayed, expt_List, opts___?OptionQ] := replaceAllExcept[expr, {r}, expt, opts];
replaceAllExcept[args___] := unexpected[ replaceAllExcept, {args}]

(* ::Subsubsection:: *)
(* replaceRepeatedExcept *)

Options[replaceRepeatedExcept] = {Heads -> {}, MaxIterations -> 20};

(*
	For ReplaceRepeated the trick with adding a rule A->A to prevent substitution of A or proceeding deeper into A does not work -> infinite loop.
	Idea: we replace expressions that should not be substituted by a string "EXCPT~h", where h is a hash code of the expression.
	When the replacement rule is actually applied, it sows a rule that establishes the backsubstitution from "EXCPT~h" to the original expression.
	Using Reap, we collect the backsubstitutions and apply them at the end.
*)
replaceRepeatedExcept[ expr_, rules_List, expt_List, opts___?OptionQ] :=
  	Module[{exptRules, heads, maxIt, new, backsubs},
  		{heads, maxIt} = {Heads, MaxIterations} /. {opts} /. Options[ replaceRepeatedExcept];
   		exptRules = Join[ 
   			Map[(# :> With[ {s = "EXCPT~"~~ToString[ Hash[#]]}, Sow[ s -> #]; s])&, expt], 
   			rules, 
   			Map[(HoldPattern[#[x___]] :> With[ {s = "EXCPT~"~~ToString[ Hash[#[x]]]}, Sow[ s -> #[x], "backsubs"]; s])&, heads]
   			];
   		{new, backsubs} = Reap[ ReplaceRepeated[ expr, exptRules, MaxIterations -> maxIt], "backsubs"];
   		If[ backsubs === {},
   			new,
   			(* else *)
   			new /. backsubs[[1]]
   		]
  	]

replaceRepeatedExcept[ expr_, r_Rule|r_RuleDelayed, expt_List, opts___?OptionQ] := replaceRepeatedExcept[ expr, {r}, expt, opts];
replaceRepeatedExcept[ args___] := unexpected[ replaceRepeatedExcept, {args}]


(* ::Subsubsection:: *)
(* applyHold *)

applyHold[ Hold[ a_], Hold[ b___]] := Hold[ a[ b]];

(* ::Subsubsection:: *)
(* joinHold *)

joinHold[ Hold[ a___], Hold[ b___]] := Hold[ a, b];

(* ::Subsubsection:: *)
(* notification *)

notification[ msg__] /; $Notebooks := MessageDialog[ StringForm[ msg]]
notification[ msg__] := Message[ StringForm[ msg]]
notification[ args___] := unexpected[ notification, {args}]


(* ::Subsubsection:: *)
(* Generic accessor for optional components in a datastructure *)

getOptionalComponent[ ds_[ ___, (Rule|RuleDelayed)[ key_String, val_], ___], key_] := val
getOptionalComponent[ ds_, key_String] := {}
getOptionalComponent[ args___] := unexpected[ getOptionalComponent, {args}]


(* ::Subsubsection:: *)
(* Log output to file *)

(* We expect the global variable $TMALogFile to be an open output stream *)

writeLog[ expr__] :=
	If[ MatchQ[ $TMALogFile, _OutputStream],
		WriteString[ $TMALogFile, DateString[], " ", expr, "\n"];
	]
writeLog[ args___] := unexpected[ writeLog, {args}]

End[]

EndPackage[]