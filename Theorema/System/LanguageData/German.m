(* Mathematica package *)

With[ {lang = "German"},
(* System Messages *)
	MessageName[Theorema, "unexpectedArgs", lang] = "Funktion `1` wurde mit unerwarteten Argumenten `2` aufgerufen.";
	MessageName[Theorema, "missingTranslation", lang] = "Fehlende \[CapitalUDoubleDot]bersetzung f\[UDoubleDot]r Zeichenkette `1` in Sprache `2`.";

(* Usage *)
	MessageName[unexpected, "usage", lang] = "unexpected[ f, {args}] beendet die Evaluation von f[args] aufgrund unerwarteter Argumente.";
]