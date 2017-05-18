(* Mathematica package *)

BeginPackage[ "System`"]

(*Lists*)
MessageName[ AllTrue, "usage"] = "";
MessageName[ AnyTrue, "usage"] = "";
MessageName[ DeleteDuplicatesBy, "usage"] = "";
MessageName[ DuplicateFreeQ, "usage"] = "";
MessageName[ FirstCase, "usage"] = "";
MessageName[ FirstPosition, "usage"] = "";
MessageName[ NoneTrue, "usage"] = "";
MessageName[ SelectFirst, "usage"] = "";

(*Associations*)
MessageName[ Association, "usage"] = "";
MessageName[ AssociationMap, "usage"] = "";
MessageName[ Key, "usage"] = "";
MessageName[ KeyDrop, "usage"] = "";
MessageName[ KeyExistsQ, "usage"] = "";
MessageName[ KeyMap, "usage"] = "";
MessageName[ Keys, "usage"] = "";
MessageName[ KeySelect, "usage"] = "";
MessageName[ KeyTake, "usage"] = "";
MessageName[ KeyValueMap, "usage"] = "";
MessageName[ Lookup, "usage"] = "";
MessageName[ Values, "usage"] = "";

Begin["`Private`"]

(* ::Section:: *)
(*Lists*)

AllTrue[ test_][ expr_, level___] :=
	AllTrue[ expr, test, level]
(* For associations, no level must be specified. *)
AllTrue[ assoc_Association, test_] :=
	Catch[
		And @@ Map[ With[ {r = test[ Last[ #]]}, If[ r === False, Throw[ False], r]]&, List @@ assoc]
	]
AllTrue[ expr_, test_, level___] :=
	Catch[
		And @@ Map[ With[ {r = test[ #]}, If[ r === False, Throw[ False], r]]&, expr, level]
	]

AnyTrue[ test_][ expr_, level___] :=
	AnyTrue[ expr, test, level]
(* For associations, no level must be specified. *)
AnyTrue[ assoc_Association, test_] :=
	Catch[
		Or @@ Map[ With[ {r = test[ Last[ #]]}, If[ TrueQ[ r], Throw[ True], r]]&, List @@ assoc]
	]
AnyTrue[ expr_, test_, level___] :=
	Catch[
		Or @@ Map[ With[ {r = test[ #]}, If[ TrueQ[ r], Throw[ True], r]]&, expr, level]
	]

NoneTrue[ test_][ expr_, level___] :=
	NoneTrue[ expr, test, level]
(* For associations, no level must be specified. *)
NoneTrue[ assoc_Association, test_] :=
	Catch[
		Nor @@ Map[ With[ {r = test[ Last[ #]]}, If[ TrueQ[ r], Throw[ False], r]]&, List @@ assoc]
	]
NoneTrue[ expr_, test_, level___] :=
	Catch[
		Nor @@ Map[ With[ {r = test[ #]}, If[ TrueQ[ r], Throw[ False], r]]&, expr, level]
	]

DeleteDuplicatesBy[ fun_][ expr_] :=
	DeleteDuplicatesBy[ expr, fun]
DeleteDuplicatesBy[ expr_, fun_] :=
	DeleteDuplicates[ expr, fun[ #1] === fun[ #2] &]

Quiet[
	(* It seems that 'DuplicateFreeQ' was added in version 9 already, although it is not documented there. *)
	DuplicateFreeQ[ expr_, args___] := (expr === DeleteDuplicates[ expr, args])
];

SetAttributes[ SelectFirst, HoldRest];
SelectFirst[ crit_][ expr_, def___] :=
	SelectFirst[ expr, crit, def]
SelectFirst[ expr_, crit_] :=
	SelectFirst[ expr, crit, Missing[ "NotFound"]]
SelectFirst[ expr_, crit_, def_] :=
	Replace[ Select[ expr, crit, 1],
		{
			Association[ _[ _, v_]] :> v,
			{e_} :> e,
			_ :> def
		}
	]

SetAttributes[ FirstCase, HoldRest];
FirstCase[ patt_][ expr_, args___] :=
	FirstCase[ expr, patt, args]
FirstCase[ expr_, patt_] :=
	FirstCase[ expr, patt, Missing[ "NotFound"], {1}]
FirstCase[ expr_, patt_, def_] :=
	FirstCase[ expr, patt, def, {1}]
FirstCase[ expr_, patt_, def_, level_, opts___?OptionQ] :=
	Replace[ Cases[ expr, patt, level, 1, opts],
		{
			{e_} :> e,
			_ :> def
		}
	]

SetAttributes[ FirstPosition, HoldRest];
FirstPosition[ patt_][ expr_, args___] :=
	FirstPosition[ expr, patt, args]
FirstPosition[ expr_, patt_] :=
	FirstPosition[ expr, patt, Missing[ "NotFound"], Infinity]
FirstPosition[ expr_, patt_, def_] :=
	FirstPosition[ expr, patt, def, Infinity]
FirstPosition[ expr_, patt_, def_, level_, opts___?OptionQ] :=
	Replace[ Position[ expr, patt, level, 1, opts],
		{
			{p_} :> p,
			_ :> def
		}
	]


(* ::Section:: *)
(*Associations*)

(* Attention! Do not rely on any particular order of the elements in an association! *)

(* If associations are constructed directly, e.g. 'Association[ 1 -> 2, 1 -> 0]', duplicate keys are *not* removed!
	Hence, use lists for constructing associations from data that could possibly contain duplicate keys. *)
Association[ l:{(_Rule|_RuleDelayed)...}] :=
	Association @@ thinRuleList[ l]

AssociationMap[ fun_][ assoc_] :=
	AssociationMap[ fun, assoc]
AssociationMap[ fun_, keys_List] :=
	Association @@ Map[ (# -> fun[ #])&, Reverse[ DeleteDuplicates[ Reverse[ keys]]]]
AssociationMap[ fun_, assoc_Association] :=
	Association[ Map[ fun, List @@ assoc]]

assoc_Association[ k_] :=
	Lookup[ assoc, k]

Association /: Part[ assoc_Association, k:(_String|_Key), rest___] :=
	Lookup[ assoc, k][[rest]]

KeyDrop[ k_][ assoc_] :=
	KeyDrop[ assoc, k]
KeyDrop[ assoc_Association, {}] :=
	assoc
KeyDrop[ assoc_Association, keys_List] :=
	Association @@ DeleteCases[ List @@ assoc, (Rule|RuleDelayed)[ Alternatives @@ keys, _]]
KeyDrop[ assoc_Association, k_] :=
	Association @@ DeleteCases[ List @@ assoc, (Rule|RuleDelayed)[ k, _]]
KeyDrop[ l:{(_Rule|_RuleDelayed)..}, k_] :=
	KeyDrop[ Association @@ thinRuleList[ l], k]
KeyDrop[ assocs_List, k_] :=
	Map[ KeyDrop[ k], assocs]

KeyTake[ k_][ assoc_] :=
	KeyTake[ assoc, k]
KeyTake[ _, {}] :=
	Association[]
KeyTake[ assoc_Association, keys_List] :=
	Association @@ Cases[ List @@ assoc, (Rule|RuleDelayed)[ Alternatives @@ keys, _]]
KeyTake[ assoc_Association, k_] :=
	Association @@ Cases[ List @@ assoc, (Rule|RuleDelayed)[ k, _]]
KeyTake[ l:{(_Rule|_RuleDelayed)..}, k_] :=
	KeyTake[ Association @@ thinRuleList[ l], k]
KeyTake[ assocs_List, k_] :=
	Map[ KeyDrop[ k], assocs]

KeySelect[ crit_][ assoc_] :=
	KeySelect[ assoc, crit]
KeySelect[ assoc_Association, crit_] :=
	Association @@ Select[ List @@ assoc, Composition[ crit, First]]
KeySelect[ l:{(_Rule|_RuleDelayed)..}, crit_] :=
	Association @@ Select[ l, Composition[ crit, First]]

KeyMap[ fun_, assoc_Association] :=
	Association @@ thinRuleList[ Replace[ List @@ assoc, ((h:(Rule|RuleDelayed))[ k_, v_]) :> h[ fun[ k], v], {1}]]

Association /: Join[ Association[], rest___Association] :=
	Join[ rest]
Association /: Join[ a_Association, Association[], rest___Association] :=
	Join[ a, rest]
Association /: Join[ a_Association, b_Association, rest___Association] :=
	Join[
		With[ {bl = List @@ b},
			Association @@ Join[
				Select[ List @@ a, (!MemberQ[ bl, (Rule|RuleDelayed)[ First[ #], _]])&],
				bl
			]
		],
		rest
	]

Association /: Append[ a_Association, b_Association] :=
	Join[ a, b]
Association /: Append[ a_Association, b:({(_Rule|_RuleDelayed)...}|_Rule|_RuleDelayed)] :=
	Join[ a, Association[ b]]

(* For associations, 'Prepend' seems to do exactly the same as 'Append' in version 10 ... *)
Association /: Prepend[ a_Association, b_Association] :=
	Join[ a, b]
Association /: Prepend[ a_Association, b:({(_Rule|_RuleDelayed)...}|_Rule|_RuleDelayed)] :=
	Join[ a, Association[ b]]

Association /: Normal[ assoc_Association] :=
	List @@ assoc

SetAttributes[ Lookup, HoldRest];
Lookup[ k_][ assoc_, def___] :=
	Lookup[ assoc, k, def]
Lookup[ assoc_, k_List, def___] :=
	Map[ Lookup[ assoc, #, def]&, k]
Lookup[ data:(_Association|{(_Rule|_RuleDelayed)..}), k_, def___] :=
	With[ {k0 = k},
		If[ ListQ[ k0],
			Lookup[ data, k0, def],
		(*else*)
			lookup[ data, k0, def]
		]
	]
Lookup[ assocs_List, k_, def___] :=
	Map[ Lookup[ #, k, def]&, assocs]

SetAttributes[ Keys, Listable];
Keys[ assoc_Association] :=
	List @@ assoc[[All, 1]]
Keys[ (Rule|RuleDelayed)[ k_, _]] :=
	k

SetAttributes[ Values, Listable];
Values[ assoc_Association] :=
	List @@ assoc[[All, 2]]
Values[ (Rule|RuleDelayed)[ _, v_]] :=
	v

KeyExistsQ[ k_][ assoc_] :=
	KeyExistsQ[ assoc, k]
KeyExistsQ[ assoc_, Key[ k_]] :=
	KeyExistsQ[ assoc, k]
KeyExistsQ[ assoc:(_Association|_List), k_] :=
	MemberQ[ assoc, (Rule|RuleDelayed)[ k, _]]

Association /: DeleteDuplicates[ assoc_Association] :=
	DeleteDuplicates[ assoc, SameQ]
Association /: DeleteDuplicates[ assoc_Association, test_] :=
	Association @@ DeleteDuplicates[ List @@ assoc, test[ Last[ #1], Last[ #2]]&]

Association /: Map[ fun_, assoc_Association, args___] :=
	Association @@ MapThread[ ReplacePart[ #1, 2 -> #2]&, {List @@ assoc, Map[ fun, Values[ assoc], args]}]

Association /: Select[ assoc_Association, crit_, args___] :=
	Association @@ Select[ List @@ assoc, Composition[ crit, Last], args]

Association /: Cases[ assoc_Association, patt_, args___] :=
	Cases[ Values[ assoc], patt, args]

(* 'DeleteCases' only works with level-specification '{1}'! *)
Association /: DeleteCases[ assoc_Association, patt_, args___] :=
	Association @@ DeleteCases[ List @@ assoc, (Rule|RuleDelayed)[ _, patt], args]

Association /: MemberQ[ assoc_Association, patt_, args___] :=
	MemberQ[ Values[ assoc], patt, args]

Association /: Position[ assoc_Association, patt_, args___] :=
	Replace[ Position[ Values[ assoc], patt, args], {i_Integer?Positive, rest___} :> {Key[ Extract[ assoc, {i, 1}]], rest}, {1}]


(* ::Subsection:: *)
(*Auxiliary Functions*)

thinRuleList[ l_List] :=
	Reverse[ DeleteDuplicatesBy[ Reverse[ l], First]]

SetAttributes[ lookup, HoldRest];
lookup[ data_, Key[ k_], def___] :=
	lookup[ data, k, def]
lookup[ data_, k_] :=
	lookup[ data, k, Missing[ "KeyAbsent", k]]
lookup[ assoc_Association, k_, def_] :=
	Replace[ k, Append[ List @@ assoc, _ :> def]]
lookup[ {rules:((_Rule|_RuleDelayed)..)}, k_, def_] :=
	Replace[ k, {rules, _ :> def}]

End[]

EndPackage[]
