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

(* ::Section:: *)
(* Public Declaration Part: executes in Theorema`Provers` *)

With[ {lang = "German"},
(* TRANSLATED *)
	MessageName[ applyOnce, "usage", lang] = "applyOnce[ prfsit] wendet eine passende Beweisregel einmal auf eine Beweissituation an.";
	MessageName[ applyOnceAndLevelSaturation, "usage", lang] = "applyOnceAndLevelSaturation[ prfsit] wendet eine passende Beweisregel einmal auf eine Beweissituation an und verwendet dann Level-Saturation Techniken.";

	MessageName[ trySeveral, "usage", lang] = "trySeveral[ prfsit] is not serious, it just duplicates the proof situation into two children. Should be a test case for exhaustive search until search depth is reached.";

(* UNTRANSLATED *)

] (* With *)


(* ::Section:: *)
(* Private Implementation Part: executes in Theorema`Provers`Private` *)

Begin["`Private`"]

With[ {lang = "German"},
(* TRANSLATED *)
	translate[ "Apply once", lang] = "Einmal anwenden";
	translate[ "Apply once + Level saturation", lang] = "Einmal anwenden + Level Saturation";

	translate[ "Try several", lang] = "Mehrere probieren";

(* UNTRANSLATED *)

] (* With *)

End[]