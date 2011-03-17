(* Mathematica package *)

With[ {lang = "German"},
(* System Messages *)
	MessageName[Theorema, "unexpectedArgs", lang] = "Funktion `1` wurde mit unerwarteten Argumenten `2` aufgerufen.";
	MessageName[Theorema, "missingTranslation", lang] = "Fehlende \[CapitalUDoubleDot]bersetzung f\[UDoubleDot]r Zeichenkette `1` in Sprache `2`.";

(* Theorema`System`Messages` *)
	MessageName[unexpected, "usage", lang] = "unexpected[ f, {args}] beendet die Evaluation von f[args] aufgrund unerwarteter Argumente.";

(* Theorema`Language`Parser` *)
	MessageName[initParser, "usage", lang] = "initParser[ ] ...";
	MessageName[processEnvironment, "usage", lang] = "processEnvironment[ expr] ...";

(* Theorema`Language`Session` *)
	MessageName[initSession, "usage", lang] = "initSession[] initialisiert die globalen Session-Variablen ...";
	MessageName[inEnvironment, "usage", lang] = "initEnvironment[] ergibt innerhalb einer Umgebung 'True' ...";

]