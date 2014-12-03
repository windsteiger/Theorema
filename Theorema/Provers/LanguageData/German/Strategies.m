(* Theorema 
    Copyright (C) 1995-2014 The Theorema Group

    This file is part of Theorema 2.0
    
    Theorema 2.0 is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Theorema 2.0 is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program. If not, see <http://www.gnu.org/licenses/>.
*)

(*
   *********************************************************************************************
   -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- 
   *********************************************************************************************
 
     If you modify this file, then a new entry must have been added to the respective file in
     the "English" directory already.

     In this file, either
      1) copy the english entry into the corresponding section named "UNTRANSLATED" (there are
         several in this file 
	       or
      2) translate the english entry and add it in correct alphabetical order here 
         (case-insensitive).
      
   *********************************************************************************************
   -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- 
   *********************************************************************************************
 *)

(* ::Section:: *)
(* Public Declaration Part: executes in Theorema`Provers` *)

With[ {lang = "German"},
(* TRANSLATED *)
	MessageName[ applyOnce, "usage", lang] = "applyOnce[ prfsit] wendet eine passende Beweisregel einmal auf eine Beweissituation an.";
	MessageName[ applyOnceAndLevelSaturation, "usage", lang] = "applyOnceAndLevelSaturation[ prfsit] wendet eine passende Beweisregel einmal auf eine Beweissituation an und verwendet dann Level-Saturation Techniken.";

	MessageName[ priorityInteractiveSaturation, "usage", lang] = "priorityInteractiveSaturation[ prfsit] wendet entweder die erste oder all passenden Beweisregeln auf die Beweissituation prfsit an (abhaengig von deren Prioritaeten), oder erlaubt dem Benutzer, eine Interaktive Regel anzuwenden.";
	
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
	
	translate[ "Priority-Interactive Strategy + Level Saturation", lang] = "Prioritaet-Interactive Strategie + Level Saturation";
	translate[ "possibleRules", lang] = "Moegliche Regeln";

	translate[ "selectInteractiveRuleHeader", lang] = "Waehle eine interactive Regel";

	translate[ "Try several", lang] = "Mehrere probieren";
	
	translate[ "!selectInteractiveRule", lang] = "keine Regel anwenden";

(* UNTRANSLATED *)

] (* With *)

End[]