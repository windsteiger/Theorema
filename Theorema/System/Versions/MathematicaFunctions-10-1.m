(* Mathematica package *)

BeginPackage[ "System`"]

(*Associations*)
MessageName[ KeyComplement, "usage"] = "";

Begin["`Private`"]


(* ::Section:: *)
(*Associations*)

Options[ KeyComplement] = {SameTest -> SameQ};
KeyComplement[ {}, ___?OptionQ] :=
	{}
KeyComplement[ {assoc_Association}, ___?OptionQ] :=
	assoc
KeyComplement[ {Association[], __}, ___?OptionQ] :=
	Association[]
KeyComplement[ {assoc_Association, rest__}, opts___?OptionQ] :=
	With[ {test = Replace[ SameTest, Join[ {opts}, Options[ KeyComplement]]]},
	With[ {drop = DeleteDuplicates[ Join @@ Replace[ {rest}, {a_Association :> Keys[ a], l_List :> l[[All, 1]]}, {1}], test]},
		If[ test === SameQ,
			KeyDrop[ assoc, drop],
		(*else*)
			KeySelect[ assoc, Function[ k, NoneTrue[ drop, TrueQ[ test[ k, #]]&]]]
		]
	]]
KeyComplement[ {list_List}, ___?OptionQ] :=
	Association[ list]
KeyComplement[ {{}, __}, ___?OptionQ] :=
	Association[]	(* 'KeyComplement' always returns an association *)
KeyComplement[ {list_List, rest__}, opts___?OptionQ] :=
	KeyComplement[ {Association[ list], rest}, opts]

End[]

EndPackage[]
