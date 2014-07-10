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

With[ {lang = "English"},
	MessageName[ openTheoremaGUI, "usage", lang] = "openTheoremaGUI[] opens the Theorema GUI.";

	MessageName[ Theorema, "usage", lang] = "Global symbol to attach messages to.";
	MessageName[ Theorema, "archiveName", lang] = "Invalid name for archive: `` . Theorema archive name must be a context string.";
	MessageName[ Theorema, "archiveNotFound", lang] = "No such archive: `` .";
	MessageName[ Theorema, "missingTranslation", lang] = "Missing translation for string `1` into language `2`.";
	MessageName[ Theorema, "unexpectedArgs", lang] = "Function `1` called with unexpected arguments `2`.";

	MessageName[ $TheoremaDirectory, "usage", lang] = "The directory where the Theorema system is installed.";
	MessageName[ $TheoremaArchiveDirectory, "usage", lang] = "The directory where Theorema stores knowledge archives.";
	MessageName[ $TheoremaArchivePath, "usage", lang] = "List of directories where Theorema searches for knowledge archives.";
	
]

