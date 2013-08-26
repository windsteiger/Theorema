(* Mathematica package *)

With[ {lang = "English"},
	MessageName[Theorema, "usage", lang] = "Global symbol to attach messages to.";
	MessageName[$TheoremaDirectory, "usage", lang] = "The directory where the Theorema system is installed.";
	MessageName[$TheoremaArchiveDirectory, "usage", lang] = "The directory where Theorema stores knowledge archives.";
	MessageName[$TheoremaArchivePath, "usage", lang] = "The directory where Theorema searches for knowledge archives.";
	MessageName[openTheoremaGUI, "usage", lang] = "openTheoremaGUI[] opens the Theorema GUI.";
	
	MessageName[Theorema, "archiveName", lang] = "Wrong name for archive: `` . Theorema archive name must be a context string.";
	MessageName[Theorema, "archiveNotFound", lang] = "No such archive: `` .";
	
]

