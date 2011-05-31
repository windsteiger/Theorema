(* Mathematica package *)

With[ {lang = "English"},
	MessageName[Theorema, "usage", lang] = "Global symbol to attach messages to.";
	MessageName[$TheoremaDirectory, "usage", lang] = "The directory where the Theorema system is installed.";
	MessageName[$TheoremaArchiveDirectory, "usage", lang] = "The directory where Theorema stores knowledge archives.";
	MessageName[$TheoremaArchivePath, "usage", lang] = "The directory where Theorema searches for knowledge archives.";
	MessageName[loadArchive, "usage", lang] = "loadArchive[ArchiveName`] loads the specified archive into the current session.";
]

