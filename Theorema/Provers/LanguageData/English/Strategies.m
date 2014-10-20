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

With[ {lang = "English"},

	MessageName[ applyOnce, "usage", lang] = "applyOnce[ prfsit] applies a matching inference rule from rules to the proof situation prfsit once.";
	MessageName[ applyOnceAndLevelSaturation, "usage", lang] = "applyOnceAndLevelSaturation[ prfsit] applies a matching inference rule to the proof situation prfsit once and then applies level saturation techniques.";
	MessageName[ priorityInteractiveSaturation, "usage", lang] = "priorityInteractiveSaturation[ prfsit] applies either the first or all matching inference rules to the proof situation prfsit (depending on their priorities), or allows the user to choose an interactive rule.";
	MessageName[ trySeveral, "usage", lang] = "trySeveral[ prfsit] tries several rules from rules to the proof situation prfsit at the same time.";

] (* With *)


(* ::Section:: *)
(* Private Implementation Part: executes in Theorema`Provers`Private` *)

Begin["`Private`"]

With[ {lang = "English"},

	translate[ "Apply once", lang] = "Apply once";
	translate[ "Apply once + Level saturation", lang] = "Apply once + Level saturation";

	translate[ "Try several", lang] = "Try several";
	
	translate[ "!selectInteractiveRule", lang] = "do not apply any rule";
	translate[ "Priority-Interactive Strategy + Level Saturation", lang] = "Priority-Interactive Strategy + Level Saturation";
	translate[ "possibleRules", lang] = "Possible Rules";
	translate[ "selectInteractiveRuleHeader", lang] = "Choose an Interactive Rule";

] (* With *)

End[]