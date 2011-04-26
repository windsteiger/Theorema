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

BeginPackage["Theorema`Interface`Language`"]

Needs["Theorema`Common`"];

Begin["`Private`"] (* Begin Private Context *) 

availableLanguages[] := Map[ FileBaseName, allLanguageFiles[]]
allLanguageFiles[] := FileNames[ "*.m", ToFileName[{$TheoremaDirectory, "Theorema", "Interface", "LanguageData"}]]

translate[ s_String] := translate[ s, $Language];
Map[ Get, allLanguageFiles[]];
translate[ s_String, lang_String] := (Message[ Theorema::missingTranslation, s, lang]; s)

End[] (* End Private Context *)

EndPackage[]