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

On[ Assert]

BeginPackage["Theorema`"];

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

(* Introduce TheoremaForm as a new format type *)
AppendTo[ $BoxForms, System`TheoremaForm];
ParentForm[ System`TheoremaForm] ^= StandardForm;

Map[ Get, FileNames[ "*.m", ToFileName[{$TheoremaDirectory, "Theorema", "Kernel", "LanguageData"}]]];

Protect[$TheoremaDirectory]; 

$TheoremaArchiveDirectory = ToFileName[{$TheoremaDirectory,"Theorema","Knowledge"}];
$TheoremaArchivePath = {$TheoremaArchiveDirectory, $HomeDirectory};

If[ TrueQ[$Notebooks],
    If[!ValueQ[`priv`welcomeScreen],
    	`priv`welcomeScreen = NotebookOpen[ToFileName[{$TheoremaDirectory,"Theorema","FrontEnd"},"Startup.nb"],
        WindowElements -> {}, WindowSize -> All, WindowFrame -> "Frameless", Deployed -> True];
        SelectionMove[ `priv`welcomeScreen, Next, Cell]],
    Print["Theorema Copyright (C) 2010 The Theorema Group.\n
    This program comes with ABSOLUTELY NO WARRANTY;\n\n    This is free software, and you are welcome to\n    redistribute it under the conditions of the\n    GNU General Public License, see <http://www.gnu.org/licenses/>."]
];


Get["Theorema`Common`"]

(* The package "Theorema`Computation`Language`" introduces the same names as "Theorema`Language`".
   Therefore, we load them from different Theorema`-contexts in order to avoid "shadowing" messages during startup.
   It is important to load "Theorema`Computation`Language`" BEFORE "Theorema`Language`", because in 
   "Theorema`Language`Syntax`" the symbols in the Computation-context must already exist.
   *)
Get["Theorema`Computation`Language`"]

EndPackage[]

BeginPackage["Theorema`"]

Get["Theorema`Language`"]
Get["Theorema`Utilities`"]
Get["Theorema`Interface`GUI`"]
Get["Theorema`Provers`"]

EndPackage[]
	
Pause[5];

If[$Notebooks && MemberQ[Notebooks[], Theorema`priv`welcomeScreen],
	NotebookClose[Theorema`priv`welcomeScreen]];

	
