(* Mathematica Package *)

BeginPackage["Theorema`Tools`"]

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

joinHold[Hold[a_], Hold[b___]] := Hold[a, b];

End[]

EndPackage[]