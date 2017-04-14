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

$TheoremaVersion = "2.0";
$TheoremaRelease = "0";

Which[ !ValueQ[ $TheoremaDirectory],
	$TheoremaDirectory = With[ {`priv`possibleDirs = Select[ $Path, (FileType[ FileNameJoin[ {#, "Theorema", "Kernel", "init.m"}]] === File)&]},
		If[ `priv`possibleDirs === {},
			Print[ "The Theorema Directory is not installed properly.\nPlease consult the installation guide."];
			Exit[],
			`priv`possibleDirs[[1]]]],
	FileType[ FileNameJoin[ {$TheoremaDirectory, "Theorema", "Kernel", "init.m"}]] =!= File,
	Print[ StringForm[ "$TheoremaDirectory=``.\nThe Theorema Directory is not installed in this directory.\nPlease consult the installation guide.",$TheoremaDirectory]];
	Exit[]
];

(* Introduce TheoremaForm as a new format type *)
If[ FreeQ[ $BoxForms, System`TheoremaForm], 
	AppendTo[ $BoxForms, System`TheoremaForm];
	ParentForm[ System`TheoremaForm] ^= StandardForm;
]

Map[ Get, FileNames[ "*.m", FileNameJoin[{$TheoremaDirectory, "Theorema", "Kernel", "LanguageData"}]]];

Protect[ $TheoremaDirectory]; 

Get[ "Theorema`Interface`ColorSchemes`"];

Map[ Get, FileNames[ "TheoremaPreferences.m", {
  FileNameJoin[ {$TheoremaDirectory, "Theorema", "Kernel"}],
  FileNameJoin[ {$UserBaseDirectory, "Applications", "Theorema", "Kernel"}]}]];   
    
$TheoremaArchivePath = {$TheoremaArchiveDirectory, $HomeDirectory};

`priv`arrowShape = {{0, 0}, {94, 0}, {107, 40}, {70, 40}, {156, 126}, {126, 156}, {40, 70}, {40, 107}, {0, 94}, {0, 0}};

`priv`RISCLogo[`priv`a_] := {TMAcolor[1], 
   Rotate[Disk[{194, 0}, 17], `priv`a, {0, 0}], 
   Rotate[Disk[{-194, 0}, 17], `priv`a, {0, 0}], 
   Rotate[Disk[{0, 194}, 17], `priv`a, {0, 0}], 
   Rotate[Disk[{0, -194}, 17], `priv`a, {0, 0}], 
   Rotate[Polygon[Map[# + {35, -175} &, `priv`arrowShape]], 
    `priv`a, {0, 0}], {AbsoluteThickness[8], 
    Rotate[Line[
      Map[#.{{Cos[Pi/2], Sin[Pi/2]}, {-Sin[Pi/2], 
            Cos[Pi/2]}} + {-35, -175} &, `priv`arrowShape]], 
     `priv`a, {0, 0}], 
    Rotate[Line[Map[# + {-175, 19} &, `priv`arrowShape]], `priv`a, {0, 0}], 
    Rotate[Line[
      Map[#.{{Cos[Pi/2], Sin[Pi/2]}, {-Sin[Pi/2], Cos[Pi/2]}} + {175, 
          19} &, `priv`arrowShape]], `priv`a, {0, 0}]}};

`priv`topleft = {TMAcolor[4], 
   Text["Original Concept by", {-230, 202}, {-1, 0}, 
    BaseStyle -> {FontFamily -> "Helvetica", FontSize -> 18}], 
   Text["Bruno Buchberger", {-230, 172}, {-1, 0}, 
    BaseStyle -> {FontFamily -> "Helvetica", FontSize -> 18}]};


`priv`topright = {TMAcolor[4], 
   Text["Developed by the", {230, 202}, {1, 0}, 
    BaseStyle -> {FontFamily -> "Helvetica", FontSize -> 18}], 
   Text["Theorema Group", {230, 172}, {1, 0}, 
    BaseStyle -> {FontFamily -> "Helvetica", FontSize -> 18}]};


`priv`bottomright = {TMAcolor[4], 
   Text["Version " <> Riffle[{$TheoremaVersion, $TheoremaRelease}, "."] <> " \[Copyright] 1995-" <> 
     ToString[Date[][[1]]], {230, -202}, {1, 0}, 
    BaseStyle -> {FontFamily -> "Helvetica", FontSize -> 12}]};


`priv`bottomleft = {TMAcolor[4], 
   Text["www.risc.jku.at/research/theorema", {-230, -202}, {-1, 0}, 
    BaseStyle -> {FontFamily -> "Helvetica", FontSize -> 11}]};

`priv`center = {TMAcolor[8], 
    Text["Theorema " <> $TheoremaVersion, {0, -3}, 
     BaseStyle -> {FontWeight -> Bold, FontSize -> 36, FontTracking -> 8}]};

showWelcomeScreen[] /; !ValueQ[`priv`welcomeScreen] && !TrueQ[ $suppressWelcomeScreen] := Module[{},
    `priv`welcomeScreen = CreatePalette[
    	Dynamic[ Graphics[{`priv`RISCLogo[Clock[2 Pi, 2, 3]], `priv`topleft, `priv`topright, `priv`bottomright, `priv`bottomleft,
    		{With[{`priv`o = Clock[1, 5, 1]}, Opacity[ If[ `priv`o < 0.4, 0.1, 3/2*`priv`o-1/2]]], `priv`center}},
    		PlotRange -> {-280, 280}, ImageSize -> {560, 560}, Background -> TMAcolor[2]]],
    	WindowFrame -> "Frameless", WindowMargins -> Automatic
    ];
    Pause[5];
]
  		
If[ TrueQ[$Notebooks],
    showWelcomeScreen[],
    Print[ "Theorema Version " <> StringJoin[ Riffle[ {$TheoremaVersion, $TheoremaRelease}, "."]] <> " (C) 2010-" <> 
     ToString[ Date[][[1]]] <> " The Theorema Group.\n
    This program comes with ABSOLUTELY NO WARRANTY;\n\n    This is free software, and you are welcome to\n    redistribute it under the conditions of the\n    GNU General Public License, see <http://www.gnu.org/licenses/>."]
];

Get[ "Theorema`Common`"]
Get[ "Theorema`System`"]

(* The package "Theorema`Computation`Language`" introduces the same names as "Theorema`Language`".
   Therefore, we load them from different Theorema`-contexts in order to avoid "shadowing" messages during startup.
   It is important to load "Theorema`Computation`Language`" BEFORE "Theorema`Language`", because in 
   "Theorema`Language`Syntax`" the symbols in the Computation-context must already exist.
   *)
Get[ "Theorema`Computation`Language`"]

EndPackage[]

BeginPackage[ "Theorema`"]

Get[ "Theorema`Language`"]
Get[ "Theorema`Computation`"]
Get[ "Theorema`Provers`"]
Get[ "Theorema`Interface`GUI`"]

EndPackage[]
	
If[ $Notebooks && MemberQ[ Notebooks[], Theorema`priv`welcomeScreen],
	NotebookClose[ Theorema`priv`welcomeScreen];
	Clear[ Theorema`priv`welcomeScreen]];

(* For documentation generation with Workbench include the following packages,
   so that their symbols appear without context *)
(*   
Needs[ "Theorema`Common`"]
*)
