(* Theorema Init File *)

(* Theorema 
    Copyright (C) 2010 The Theorema Group

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*)

(* 
Theorema editor: W. Windsteiger
Author(s):       W. Windsteiger

What is the purpose of the Theorema editor? Read more in /ProgrammersDoc/Guidelines.nb#1871658360
*)

BeginPackage["Theorema`"];

Theorema::usage = "Global symbol to attach messages to.";

Which[!ValueQ[$TheoremaDirectory],
	$TheoremaDirectory=With[{`priv`possibleDirs=Select[$Path,(FileType[ToFileName[{#,"Theorema","Kernel"},"init.m"]]===File)&]},
		If[`priv`possibleDirs==={},
			Print["The Theorema Directory is not installed properly.\nPlease consult the installation guide."];
			Exit[],
			`priv`possibleDirs[[1]]]],
	FileType[ToFileName[{$TheoremaDirectory,"Theorema","Kernel"},"init.m"]]=!=File,
	Print[StringForm["$TheoremaDirectory=``.\nThe Theorema Directory is not installed in this directory.\nPlease consult the installation guide.",$TheoremaDirectory]];
	Exit[]
];

Protect[$TheoremaDirectory]; 

If[ TrueQ[$Notebooks],
    If[!ValueQ[`priv`welcomeScreen],
    	`priv`welcomeScreen = NotebookOpen[ToFileName[{$TheoremaDirectory,"Theorema","FrontEnd"},"Startup.nb"],
        WindowElements -> {}, WindowSize -> All, WindowFrame -> "Frameless", Deployed -> True]],
    Print["Theorema Copyright (C) 2010 The Theorema Group.\n
    This program comes with ABSOLUTELY NO WARRANTY;\n\n    This is free software, and you are welcome to\n    redistribute it under the conditions of the\n    GNU General Public License, see <http://www.gnu.org/licenses/>."]
];

EndPackage[]


Get["Theorema`GUI`GUI`"]
		
Pause[5];

If[$Notebooks && MemberQ[Notebooks[], Theorema`priv`welcomeScreen],
	NotebookClose[Theorema`priv`welcomeScreen]];

	
