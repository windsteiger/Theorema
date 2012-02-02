(* Mathematica Package *)

BeginPackage["Theorema`Utilities`"]

Needs["Theorema`Common`"]

Begin["`Private`"]


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
(* joinKB *)

joinKB[ kb1_List, kb2_List] := DeleteDuplicates[ Join[ kb1, kb2], #1[[1]] === #2[[1]]&]
joinKB[ args___] := unexpected[ joinKB, {args}]


(* ::Subsubsection:: *)
(* notification *)

notification[msg__] /; $Notebooks := MessageDialog[ StringForm[msg]]
notification[msg__] := Message[ StringForm[msg]]
notification[args___] := unexpected[notification, {args}]

End[]

EndPackage[]