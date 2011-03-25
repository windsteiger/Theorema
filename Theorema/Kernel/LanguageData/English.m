(* Mathematica package *)

With[ {lang = "English"},
	MessageName[Theorema, "usage", lang] = "Global symbol to attach messages to.";
	MessageName[$TheoremaDirectory, "usage", lang] = "The directory where the Theorema system is installed.";
	MessageName[DEFINITION, "usage", lang] = "DEFINITION opens a definition environment ...";
	MessageName[COMPUTE, "usage", lang] = "COMPUTE opens a computation environment ...";
	MessageName[\[GraySquare], "usage", lang] = "\[GraySquare] closes an environment ...";
	MessageName[QU$, "usage", lang] = "A marker introduced during the parsing process that temporarily marks quantified variables.";
	MessageName[VAR$, "usage", lang] = "";
	MessageName[RNG$, "usage", lang] = "";
	MessageName[SIMPRNG$, "usage", lang] = "SIMPRNG[x] usually denotes that the variable x ranges over the universe.";
	MessageName[forallTM, "usage", lang] = "";

]
