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

BeginPackage[ "Theorema`Language`Unification`"]

Needs[ "Theorema`Common`"]
Needs[ "Theorema`Language`"]

(* Exported symbols added here with SymbolName::usage *)  

Begin[ "`Private`"] (* Begin Private Context *) 

(* ::Section:: *)
(* Unification *)

(* 
    Options: maximumSolutions specifies the maximal number of solutions to be computed,
    maximumWidth imposes the limit on application of the widening rule for each sequence variable, 
    restricting the width (lenght) of the sequence the variable can be instantiated with,
    commutative specifies the list of commutative function symbols.  
*)

Options[ unification] = {maximumUnifiers -> 5, maximumWidth -> 7, commutative -> {}}

(*
   unification[s_, t_, opt___] takes as input two expressions s and t, together with the options opt
   and computes a pair of lists {{e_1,...,e_n}, {subst_1,...,subst_n}} such that for each 1 =< i =< n,
   subst_i is a unifier (modulo alpha-equivalence) of s and t, and e_i is a common instance of s and t
   under subst_i (modulo alpha-equivalence). The (multi-)set {subst_1,...,subst_n} is not minimized 
   with respect to subsumption ordering, hence it may contain two substitutions such that one is 
   more general than the other.
*)

unification[ s_, s_, ___?OptionQ] := {{s}, {{}}}
unification[ s_, t_, opt___?OptionQ] :=
    Module[ {maxUnifiers, maxWidth, commutativeSymbols, unifierCounter = 0, widthCounter = 0, commonInstances = {}, unifiers = {}, outputAcc, output, 
    	     sVariant, sBoundVars, tVariant, tBoundVars, renamingSubst = {}, metaVariables }, 
    	{maxUnifiers, maxWidth, commutativeSymbols} = {maximumUnifiers, maximumWidth, commutative} /. {opt} /. Options[ unification];
        outputAcc = {commonInstances, unifiers};
    	Block[ {$RecursionLimit = Infinity},
            {sVariant, sBoundVars} = alphaRenaming[ s, {}];
            {tVariant, tBoundVars} = alphaRenaming[ t, {}];
            output = 
               unificationAux[ {up[{{sVariant, tVariant, widthCounter}}, sBoundVars, tBoundVars, renamingSubst, sVariant, unifiers]}, 
                   outputAcc, unifierCounter, maxUnifiers, maxWidth, Append[ commutativeSymbols, commutativeWrapper[ Unique["c"]]]];
        ];
    	(* The output might contain mappings for variables introduced at run-time. 
    	   They should be discarded from the final result. Only meta variables and
    	   free variables of s and t are relevant. *)
    	metaVariables = Cases[ {s,t}, META$[_, _, _], {0, Infinity}, Heads -> True];
    	{output[[1]], restrictSubstitutions[ output[[2]], Join[ freeVariables[{s, t}], metaVariables]]}
    ]
unification[ args___] := unexpected[ unification, {args}]

unifiable[ s_, t_, opt___?OptionQ] := unification[ s, t, opt] =!= {$Failed, $Failed}
unifiable[ args___] := unexpected[ unifiable, {args}]


(* ::Section:: *)
(* matches *)

(* As a quick solution, to have something, we provide "matching" as a special case of unification. A more efficient implementation taking
	into account the special case will be provided soon. *)

(* instantiation[ s_, t_, opt___?OptionQ] gives a list of substitutions for free variables that transforms s into t. If the result is {}, then s=t. 
	If the result is $Failed, then t is not an instance of s. *)	
instantiation[ s_, t_, opt___?OptionQ] :=
	Module[ {inst, unif, i, subst = $Failed},
        {inst, unif} = unification[ s, t, opt];
        (* If non-unifiable: $Failed has length 0 and loop will be skipped *)
        Do[
            If[ MatchQ[ t, inst[[i]] /. Map[ var2pattRule, boundVariables[ inst]]],
                (* replace the bound variables by patterns and match. If successful then remember unifying substitution und exit the loop.
                    If no bound variables, then inst /. {} returns inst without effort (no need to implement seperate case.*)
                 subst = unif[[i]];
                Break[]
            ], 
        {i, Length[ inst]}
        ];
        subst
    ]		
instantiation[ args___] := unexpected[ instantiation, {args}]

(* Intended result: 
  for sequence variables: VAR$[ SEQx[ n]] -> VAR$[ SEQx[ n_]]
  for individual variables: VAR$[ n] -> VAR$[ n_]
*)
var2pattRule[ v_VAR$] := v -> Map[ Pattern[ #, Blank[]]&, v, {Depth[v]-1}]
var2pattRule[ args___] := unexpected[ var2pattRule, {args}]

matches[ s_, t_, opt___?OptionQ] := instantiation[ s, t, opt] =!= $Failed
matches[ args___] := unexpected[ matches, {args}]

	
(* ::Section:: *)
(* Auxiliary function for unification *)	

unificationAux[ {}, output_, _, _, _, _] :=
    If[ output === {{}, {}}, {$Failed, $Failed}, output /. {f_[] /; !MemberQ[ {List, Sequence}, f] -> f}]
unificationAux[ _, output_, unifierCounter_, maxUnifiers_, _, _] /; unifierCounter >= maxUnifiers :=
    If[ output === {{}, {}}, {$Failed, $Failed}, output /. {f_[] /; !MemberQ[ {List, Sequence}, f] -> f}]
unificationAux[ {solved[f_[], unifier_], unifProblems___}, {{mcis___}, {unifiers___}}, unifierCounter_, maxUnifiers_, maxWidth_, commutativeSymbols_] :=
    unificationAux[{unifProblems}, {{mcis, f}, {unifiers, unifier}}, unifierCounter+1, maxUnifiers, maxWidth, commutativeSymbols]
unificationAux[ {solved[t_, unifier_], unifProblems___}, {{mcis___}, {unifiers___}}, unifierCounter_, maxUnifiers_, maxWidth_, commutativeSymbols_] :=
    unificationAux[ {unifProblems}, {{mcis,t/.unifier},{unifiers,unifier}}, unifierCounter+1, maxUnifiers, maxWidth, commutativeSymbols]
unificationAux[ {unifProblem_,unifProblems___}, output_, unifierCounter_, maxUnifiers_, maxWidth_, commutativeSymbols_] :=
    Module[{generatedProblems, newProblems},
    	generatedProblems = transform[ unifProblem, maxWidth, commutativeSymbols];
    	newProblems = Join[ generatedProblems, {unifProblems}];
    	unificationAux[ newProblems, output, unifierCounter, maxUnifiers, maxWidth, commutativeSymbols]
    ]
    
(* ::Section:: *)
(*  Transforming unification problems into lists of unification problems *)     

(*  Nothing to be transformed. The unification problem is solved *)
transform[ up[{}, _, _, _, term_, unifier_], _, _] := {solved[term, unifier]}
(*  The first equation in the unification problem exceeds the depth limit. Fail. 
    The problem can not be solved within the specified constraints. *)
transform[ up[{{_, _, widthCounter_}, ___}, _, _, _, _, _], maxWidth_, _] /; widthCounter >= maxWidth := {}
(*  The first equation in the unification problem is trivial. It is removed. *)
transform[ up[{{l_, r_, _}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] /; ((l/.renaming) === r) := 
	{up[{equations}, lBoundVars, rBoundVars, renaming, term, subst]}
(*  Identifying f with f[]  *) 
transform[ up[{{l_, f_Symbol, widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] := 
    {up[{{l, f[], widthCounter}, equations}, lBoundVars, rBoundVars, renaming, term, subst]}
transform[ up[{{f_Symbol, r_, widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] := 
    {up[{{f[], r, widthCounter}, equations}, lBoundVars, rBoundVars, renaming, term, subst]}
    
(*  
    A bound variable can be unified only to another bound variable (modulo alpha-equivalence), provided that it is not
    already mapped to some other bound variable. Any other attempt leads to failure. 
*)    
transform[ up[{{VAR$[x_], VAR$[y_], _}, equations___}, lbv:{___, VAR$[x_], ___}, rbv:{___, VAR$[y_], ___}, renaming_, term_, subst_], _, _] :=
    If[ (VAR$[x]/.renaming) === VAR$[x], 
    	{up[{equations}, lbv, rbv, Append[renaming, VAR$[x]->VAR$[y]], term, subst]}, 
    		If[ (VAR$[x]/.renaming) === VAR$[y], {up[{equations}, lbv, rbv, renaming, term, subst]}, {}]
    ]
transform[ up[{{VAR$[x_], _, _}, ___}, {___, VAR$[x_], ___}, _, _, _, _], _, _] := {}
transform[ up[{{_, VAR$[y_], _}, ___}, _, {___, VAR$[y_], ___}, _, _, _], _, _] := {}
transform[ up[{{f_[VAR$[x_], largs___], f_[VAR$[y_], rargs___], widthCounter_}, equations___}, lbv:{___, VAR$[x_], ___}, rbv:{___, VAR$[y_], ___}, renaming_, term_, subst_], _, _] :=
    If[ (VAR$[x]/.renaming) === VAR$[x], 
    	{up[{{f[largs], f[rargs], widthCounter}, equations}, lbv, rbv, Append[renaming, VAR$[x]->VAR$[y]], term, subst]}, 
    	   If[ (VAR$[x]/.renaming) === VAR$[y], {up[{{f[largs], f[rargs], widthCounter}, equations}, lbv, rbv, renaming, term, subst]}, {}]
    ] 
transform[ up[{{f_[VAR$[x_],___], _, _}, ___}, {___, VAR$[x_], ___}, _, _, _, _], _, _] := {}
transform[ up[{{_, f_[VAR$[y_],___], _}, ___}, _, {___, VAR$[y_], ___}, _, _, _], _, _] := {}
    
(*  
    Elimination of a variable with a single expression, which is not that variable itself.
    The situation to which the first four rules apply should be very rare:
        Equations between a sequence variable and an expression can arise only if they are given as such in the input.
        Otherwise, the unification rules do not cause such equations to be generated.
    The last two rules apply when one side is a individual variable and the other side is not a sequence variable.
        These are the only rules that eliminate individual variables.
*)
(*  In the next two rules, t can be any term  *)  
transform[ up[{{VAR$[SEQ0$[x_]], t_, _}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    If[ FreeQ[ t, VAR$[SEQ0$[x]]], {up[{equations}/.{VAR$[SEQ0$[x]]->t}, lBoundVars, rBoundVars, renaming, term, compose[subst, {VAR$[SEQ0$[x]]->t}]]}, {}]
transform[ up[{{t_, VAR$[SEQ0$[x_]], _}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    If[ FreeQ[ t, VAR$[SEQ0$[x]]], {up[{equations}/.{VAR$[SEQ0$[x]]->t}, lBoundVars, rBoundVars, renaming, term, compose[subst, {VAR$[SEQ0$[x]]->t}]]}, {}]
(*  In the next two rules, t can not be a projectable sequence variable  *)
transform[ up[{{VAR$[SEQ1$[x_]], t_, _}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    If[ FreeQ[ t, VAR$[SEQ1$[x]]], {up[{equations}/.{VAR$[SEQ1$[x]]->t}, lBoundVars, rBoundVars, renaming, term, compose[subst, {VAR$[SEQ1$[x]]->t}]]}, {}]
transform[ up[{{t_, VAR$[SEQ1$[x_]], _}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    If[ FreeQ[ t, VAR$[SEQ1$[x]]], {up[{equations}/.{VAR$[SEQ1$[x]]->t}, lBoundVars, rBoundVars, renaming, term, compose[subst, {VAR$[SEQ1$[x]]->t}]]}, {}]
(*  In the next two rules, t can not be a sequence variable  *)
transform[ up[{{VAR$[x_], t_, _}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    If[ FreeQ[ t, VAR$[x]], {up[{equations}/.{VAR$[x]->t}, lBoundVars, rBoundVars, renaming, term, compose[subst, {VAR$[x]->t}]]}, {}]
transform[ up[{{t_, VAR$[x_], _}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    If[ FreeQ[ t, VAR$[x]], {up[{equations}/.{VAR$[x]->t}, lBoundVars, rBoundVars, renaming, term, compose[subst, {VAR$[x]->t}]]}, {}]

(*  
    Elimination of a meta-variable with a single expression,  which is not that variable itself.
    The situations where a sequence meta-variable appears as a side of a unification problem should be very rare.
    In the first two rules y can be any variable name or a sequence object.
*)
transform[ up[{{m1:META$[SEQ0$[x_], _, fixedConstantList1_], m2:META$[y_, _, fixedConstantList2_], _}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    Module[ {intersection, newVar, metaNew},
    	intersection = Intersection[ fixedConstantList1, fixedConstantList2];
    	newVar = If[ (Head[ y] === SEQ0$) || (Head[ y] === SEQ1$), Head[y][Unique["z"]], Unique["z"]];
    	metaNew = META$[newVar, 0, intersection];
        {up[{equations}/.{m1->metaNew, m2->metaNew}, lBoundVars, rBoundVars, renaming, term, compose[subst, {m1->metaNew, m2->metaNew}]]}]
transform[ up[{{m1:META$[y_, _, fixedConstantList1_], m2:META$[SEQ0$[x_], _, fixedConstantList2_], _}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    Module[ {intersection, newVar, metaNew},
        intersection = Intersection[ fixedConstantList1, fixedConstantList2];
        newVar = If[ (Head[ y] === SEQ0$) || (Head[ y] === SEQ1$), Head[y][Unique["z"]], Unique["z"]];
        metaNew = META$[newVar, 0, intersection];
        {up[{equations}/.{m1->metaNew, m2->metaNew}, lBoundVars, rBoundVars, renaming, term, compose[subst, {m1->metaNew, m2->metaNew}]]}]
(*   In the two rules below, y can not be a projectable sequence object    *)        
transform[ up[{{m1:META$[SEQ1$[x_], _, fixedConstantList1_], m2:META$[y_, _, fixedConstantList2_], _}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    Module[ {intersection, newVar, metaNew},
        intersection = Intersection[ fixedConstantList1, fixedConstantList2]; 
        newVar = If[ Head[ y] === SEQ1$, SEQ1$[Unique["z"]], Unique["z"]];
        metaNew = META$[newVar, 0, intersection];
        up[{equations}/.{m1->metaNew, m2->metaNew}, lBoundVars, rBoundVars, renaming, term, compose[subst, {m1->metaNew, m2->metaNew}]]]
transform[ up[{{m1:META$[y_, _, fixedConstantList1_], m2:META$[SEQ1$[x_], _, fixedConstantList2_], _}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    Module[ {intersection, newVar, metaNew},
        intersection = Intersection[ fixedConstantList1, fixedConstantList2]; 
        newVar = If[ Head[ y] === SEQ1$, SEQ1$[Unique["z"]], Unique["z"]];
        metaNew = META$[newVar, 0, intersection];
        up[{equations}/.{m1->metaNew, m2->metaNew}, lBoundVars, rBoundVars, renaming, term, compose[subst, {m1->metaNew, m2->metaNew}]]]
(*   In the rule below, x1 and x2 can not be (projectable or non-projectable) sequence objects   *)        
transform[ up[{{m1:META$[x1_, _, fixedConstantList1_], m2:META$[x2_, _, fixedConstantList2_], _}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    Module[ {intersection, metaNew},
        intersection = Intersection[ fixedConstantList1, fixedConstantList2]; 
        metaNew = META$[Unique["y"], 0, intersection];
        {up[{equations}/.{m1->metaNew, m2->metaNew}, lBoundVars, rBoundVars, renaming, term, compose[subst, {m1->metaNew, m2->metaNew}]]}]
(*  In the next two rules, t can not be a variable or a meta-variable *)  
transform[ up[{{m:META$[(SEQ0$|SEQ1$)[x_], _, fixedConstantList_], t_, _}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    If[ FreeQ[ t, m], 
    	If[ containsExtraFixedConstant[ t, fixedConstantList], {}, {up[{equations}/.{m->t}, lBoundVars, rBoundVars, renaming, term, compose[subst, {m->t}]]}], 
    	   {}]
transform[ up[{{t_, m:META$[(SEQ0$|SEQ1$)[x_], _, fixedConstantList_], _}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    If[ FreeQ[ t, m], 
        If[ containsExtraFixedConstant[ t, fixedConstantList], {}, {up[{equations}/.{m->t}, lBoundVars, rBoundVars, renaming, term, compose[subst, {m->t}]]}], 
            {}]
(*  In the next two rules, t can not be a variable or a sequence meta-variable  *)
transform[ up[{{m:META$[x_, _, fixedConstantList_], t_, _}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    If[ FreeQ[ t, m], 
        If[ containsExtraFixedConstant[ t, fixedConstantList], {}, {up[{equations}/.{m->t}, lBoundVars, rBoundVars, renaming, term, compose[subst, {m->t}]]}], 
            {}]
transform[ up[{{t_, m:META$[x_, _, fixedConstantList_], _}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    If[ FreeQ[ t, m], 
        If[ containsExtraFixedConstant[ t, fixedConstantList], {}, {up[{equations}/.{m->t}, lBoundVars, rBoundVars, renaming, term, compose[subst, {m->t}]]}], 
            {}]


(*
    Two expressions l and r to be unified have the same head f and a non-projectable sequence variable 
        VAR$[SEQ1$[x]] appears under f.
    f != VAR$.
    VAR$[SEQ1$[x]] is replaced with a sequence of two variables VAR$[x1],VAR$[SEQ0$[x2]], where
        VAR$[x1] is a fresh individual variable, and
        VAR$[SEQ0$[x2]] is a fresh projectable sequence variable.
*)  
transform[ up[{{l:f_[VAR$[SEQ1$[x_]], args1___], r:f_[args2___], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    Module[{x1 = Unique[ToString[x]], x2 = Unique[ToString[x]], sub},
    	sub = {VAR$[SEQ1$[x]] -> Sequence[VAR$[x1], VAR$[SEQ0$[x2]]]};
        {up[{{l/.sub, r/.sub, widthCounter}, Sequence@@({equations}/.sub)}, lBoundVars, rBoundVars, renaming, term, compose[subst, sub]]}]
transform[ up[{{l:f_[args1___], r:f_[VAR$[SEQ1$[x_]], args2___], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    Module[{x1 = Unique[ToString[x]], x2 = Unique[ToString[x]], sub},
        sub = {VAR$[SEQ1$[x]] -> Sequence[VAR$[x1], VAR$[SEQ0$[x2]]]};
        {up[{{l/.sub, r/.sub, widthCounter}, Sequence@@({equations}/.sub)}, lBoundVars, rBoundVars, renaming, term, compose[subst, sub]]}]
        
(*
    Two expressions l and r to be unified have the same head f and a non-projectable sequence meta-variable 
        META$[SEQ1$[x],l] appears under f.
    f != VAR$.
    META$[SEQ1$[x],l] is replaced with a sequence of two variables META$[x1,l],META$[SEQ0$[x2],l], where
        META$[x1,l] is a fresh individual meta-variable, and
        META$[SEQ0$[x2],l] is a fresh projectable sequence variable.
*)  
transform[ up[{{l:f_[META$[SEQ1$[x_], n_, fixedConstants_], args1___], r:f_[args2___], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    Module[{x1 = Unique[ToString[x]], x2 = Unique[ToString[x]], sub},
        sub = {META$[SEQ1$[x], n, fixedConstants] -> Sequence[META$[x1, 0, fixedConstants], META$[SEQ0$[x2], 0, fixedConstants]]};
        {up[{{l/.sub, r/.sub, widthCounter}, Sequence@@({equations}/.sub)}, lBoundVars, rBoundVars, renaming, term, compose[subst, sub]]}]
transform[ up[{{l:f_[args1___], r:f_[META$[SEQ1$[x_], n_, fixedConstants_], args2___], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    Module[{x1 = Unique[ToString[x]], x2 = Unique[ToString[x]], sub},
        sub = {META$[SEQ1$[x], n, fixedConstants] -> Sequence[META$[x1, 0, fixedConstants], META$[SEQ0$[x2], 0, fixedConstants]]};
        {up[{{l/.sub, r/.sub, widthCounter}, Sequence@@({equations}/.sub)}, lBoundVars, rBoundVars, renaming, term, compose[subst, sub]]}]
        
(* 
    In the first equation, two expressions l and r to be unified have the same head f, 
        a projectable sequence variable VAR$[SEQ0$[x]] appears under f, and
        the expression in the opposite side has no arguments.
    f != VAR$.
    The projection method applies, replacing VAR$[SEQ0$[x]] with the empty sequence.
*)
transform[ up[{{l:f_[VAR$[SEQ0$[x_]], args___], r:f_[], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    With[{subP = {VAR$[SEQ0$[x]] -> Sequence[]}},
        {up[{{f[args]/.subP, r/.subP, widthCounter}, Sequence@@({equations}/.subP)}, lBoundVars, rBoundVars, renaming, term, compose[subst, subP]]}]
transform[ up[{{l:f_[], r:f_[VAR$[SEQ0$[x_]], args___], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    With[{subP = {VAR$[SEQ0$[x]] -> Sequence[]}},
        {up[{{l/.subP, f[args]/.subP, widthCounter}, Sequence@@({equations}/.subP)}, lBoundVars, rBoundVars, renaming, term, compose[subst, subP]]}] 
        
(* 
    In the first equation, two expressions l and r to be unified have the same head f, 
        a projectable sequence meta-variable META$[SEQ0$[x], l] appears under f, and
        the expression in the opposite side has no arguments.
    f != VAR$.
    The projection method applies, replacing META$[SEQ0$[x], l] with the empty sequence.
*)
transform[ up[{{l:f_[META$[SEQ0$[x_], n_, fixedConstants_], args___], r:f_[], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    With[{subP = {META$[SEQ0$[x], n, fixedConstants] -> Sequence[]}},
        {up[{{f[args]/.subP, r/.subP, widthCounter}, Sequence@@({equations}/.subP)}, lBoundVars, rBoundVars, renaming, term, compose[subst, subP]]}]
transform[ up[{{l:f_[], r:f_[META$[SEQ0$[x_], n_, fixedConstants_], args___], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    With[{subP = {META$[SEQ0$[x], n, fixedConstants] -> Sequence[]}},
        {up[{{l/.subP, f[args]/.subP, widthCounter}, Sequence@@({equations}/.subP)}, lBoundVars, rBoundVars, renaming, term, compose[subst, subP]]}] 
                 
(*   
     In the first equation, two expressions l and r to be unified have the same commutative head f, 
         a projectable sequence variable VAR$[SEQ0$[x]] appears under f, and 
         the expression in the opposite side has at least one argument.
     f != VAR$.
     An incomplete method of expression decomposition applies. It will replace each sequence variable under f with a sequence of individual variables. 
     Details can be seen at the definition of the function decompose.   
*)
transform[ up[{{l:f_[VAR$[SEQ0$[x_]], args1___], r:f_[args2__], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], maxWidth_, {commSymb1___,f_,commSymb2___}] :=
    decompose[ up[{{l, r, widthCounter}, equations}, lBoundVars, rBoundVars, renaming, term, subst], maxWidth, f]
transform[ up[{{l:f_[args1__], r:f_[VAR$[SEQ0$[x_]], args2___], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], maxWidth_, {commSymb1___,f_,commSymb2___}] :=
    decompose[ up[{{l, r, widthCounter}, equations}, lBoundVars, rBoundVars, renaming, term, subst], maxWidth, f]
transform[ up[{{l:f_[VAR$[SEQ0$[x_]], args1___], r:f_[args2__], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], maxWidth_, {commSymb1___,commutativeWrapper[f_],commSymb2___}] :=
    decompose[ up[{{l, r, widthCounter}, equations}, lBoundVars, rBoundVars, renaming, term, subst], maxWidth, commutativeWrapper[f]]
transform[ up[{{l:f_[args1__], r:f_[VAR$[SEQ0$[x_]], args2___], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], maxWidth_, {commSymb1___,commutativeWrapper[f_],commSymb2___}] :=
    decompose[ up[{{l, r, widthCounter}, equations}, lBoundVars, rBoundVars, renaming, term, subst], maxWidth, commutativeWrapper[f]]   
    
(*   
     In the first equation, two expressions l and r to be unified have the same commutative head f, 
         a projectable sequence meta-variable META$[SEQ0$[x], l] appears under f, and 
         the expression in the opposite side has at least one argument.
     f != VAR$.
     An incomplete method of expression decomposition applies. It will replace each sequence variable under f with a sequence of individual meta-variables. 
     Details can be seen at the definition of the function decompose.   
*) 
transform[ up[{{l:f_[META$[SEQ0$[x_], _, fixedConstants_], args1___], r:f_[args2__], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], maxWidth_, {commSymb1___,f_,commSymb2___}] :=
    decompose[ up[{{l, r, widthCounter}, equations}, lBoundVars, rBoundVars, renaming, term, subst], maxWidth, f]
transform[ up[{{l:f_[args1__], r:f_[META$[SEQ0$[x_], _, fixedConstants_], args2___], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], maxWidth_, {commSymb1___,f_,commSymb2___}] :=
    decompose[ up[{{l, r, widthCounter}, equations}, lBoundVars, rBoundVars, renaming, term, subst], maxWidth, f]
transform[ up[{{l:f_[META$[SEQ0$[x_], _, fixedConstants_], args1___], r:f_[args2__], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], maxWidth_, {commSymb1___,commutativeWrapper[f_],commSymb2___}] :=
    decompose[ up[{{l, r, widthCounter}, equations}, lBoundVars, rBoundVars, renaming, term, subst], maxWidth, commutativeWrapper[f]]
transform[ up[{{l:f_[args1__], r:f_[META$[SEQ0$[x_], _, fixedConstants_], args2___], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], maxWidth_, {commSymb1___,commutativeWrapper[f_],commSymb2___}] :=
    decompose[ up[{{l, r, widthCounter}, equations}, lBoundVars, rBoundVars, renaming, term, subst], maxWidth, commutativeWrapper[f]]      
(*
    In the first equation, two expressions l and r to be unified have the same free head f,
        the first argument in l is the projectable sequence variable VAR$[SEQ0$[x]], and
        the first argument in r is the projectable sequence variable VAR$[SEQ0$[y]].
    f != VAR$.
    A complete method of elimination and two widenings is applied.
    Elimination eliminated VAR$[SEQ0$[x]], replacing it with VAR$[SEQ0$[y]].
    The first widening substitution widens VAR$[SEQ0$[x]], 
        replacing VAR$[SEQ0$[x]] with a sequence VAR$[SEQ0$[y]],VAR$[SEQ0$[x]].
    The second widening substitution widens VAR$[SEQ0$[y]],
        replacing VAR$[SEQ0$[y]] with a sequence VAR$[SEQ0$[x]],VAR$[SEQ0$[y]].
*) 
transform[ up[{{l:f_[VAR$[SEQ0$[x_]], args1___], r:f_[VAR$[SEQ0$[y_]], args2___], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    Module[{subE, subW1, subW2, upE, upW1, upW2, freshX, freshY},
    	freshX = ToString[Unique[x]];
    	freshY = ToString[Unique[y]];
    	subE  = {VAR$[SEQ0$[x]] -> VAR$[SEQ0$[y]]};
    	subW1 = {VAR$[SEQ0$[x]] -> Sequence[VAR$[SEQ0$[y]], VAR$[SEQ1$[freshX]]]};
    	subW2 = {VAR$[SEQ0$[y]] -> Sequence[VAR$[SEQ0$[x]], VAR$[SEQ1$[freshY]]]};
        upE  = up[{{f[args1]/.subE, f[args2]/.subE, widthCounter}, Sequence@@({equations}/.subE)}, lBoundVars, rBoundVars, renaming, term, compose[subst,subE]];
        upW1 = up[{{Drop[l/.subW1,1], f[args2]/.subW1, widthCounter+1}, Sequence@@({equations}/.subW1)}, lBoundVars, rBoundVars, renaming, term, compose[subst,subW1]];
        upW2 = up[{{f[args1]/.subW2, Drop[r/.subW2,1], widthCounter+1}, Sequence@@({equations}/.subW2)}, lBoundVars, rBoundVars, renaming, term, compose[subst,subW2]];
        {upE, upW1, upW2}
    ]
(*
    In the first equation, two expressions l and r to be unified have the same free head f,
        the first argument in l is the projectable sequence meta-variable META$[SEQ0$[x],l1], and
        the first argument in r is the projectable sequence meta-variable META$[SEQ0$[y],l2].
    f != VAR$.
    A complete method of elimination and two widenings is applied.
    Elimination eliminated META$[SEQ0$[x],l1] and META$[SEQ0$[y],l2], replacing it with META$[SEQ0$[Unique["z"],Intersection[l1,l2]]].
    The first widening substitution widens META$[SEQ0$[x],l1], 
        replacing META$[SEQ0$[y], l2] with META$[SEQ0$[Unique["z"],Intersection[l1,l2]]] and
        META$[SEQ0$[x],l1] with a sequence META$[SEQ0$[Unique["z"],Intersection[l1,l2]]],META$[SEQ0$[Unique[x]],Intersection[l1,l2]].
    The second widening substitution widens META$[SEQ0$[y],l2],
        replacing META$[SEQ0$[x], l1] with META$[SEQ0$[Unique["z"],Intersection[l1,l2]]] and
        META$[SEQ0$[y],l1] with a sequence META$[SEQ0$[Unique["z"],Intersection[l1,l2]]],META$[SEQ0$[Unique[y]],Intersection[l1,l2]].
*)     
transform[ up[{{l:f_[META$[SEQ0$[x_], nx_, fixedConstants1_], args1___], r:f_[META$[SEQ0$[y_], ny_, fixedConstants2_], args2___], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    Module[{subE, subW1, subW2, upE, upW1, upW2, freshX, freshY, freshZ, intersect},
        freshX = ToString[Unique[x]];
        freshY = ToString[Unique[y]];
        freshZ = ToString[Unique["z"]];
        intersect = Intersection[ fixedConstants1, fixedConstants2];
        subE  = {META$[SEQ0$[x], nx, fixedConstants1] -> META$[SEQ0$[freshZ], 0, intersect], META$[SEQ0$[y], ny, fixedConstants2] -> META$[SEQ0$[freshZ], 0, intersect]};
        subW1 = {META$[SEQ0$[x], nx, fixedConstants1] -> Sequence[META$[SEQ0$[freshZ], 0, intersect], META$[SEQ1$[freshX], 0, intersect]], META$[SEQ0$[y], ny, fixedConstants2] -> META$[SEQ0$[freshZ], 0, intersect]};
        subW2 = {META$[SEQ0$[x], nx, fixedConstants1] -> META$[SEQ0$[freshZ], 0, intersect], META$[SEQ0$[y], ny, fixedConstants2] -> Sequence[META$[SEQ0$[freshZ], 0, intersect], META$[SEQ1$[freshY], 0, intersect]]};
        upE  = up[{{f[args1]/.subE, f[args2]/.subE, widthCounter}, Sequence@@({equations}/.subE)}, lBoundVars, rBoundVars, renaming, term, compose[subst,subE]];
        upW1 = up[{{Drop[l/.subW1,1], f[args2]/.subW1, widthCounter+1}, Sequence@@({equations}/.subW1)}, lBoundVars, rBoundVars, renaming, term, compose[subst,subW1]];
        upW2 = up[{{f[args1]/.subW2, Drop[r/.subW2,1], widthCounter+1}, Sequence@@({equations}/.subW2)}, lBoundVars, rBoundVars, renaming, term, compose[subst,subW2]];
        {upE, upW1, upW2}
    ]    
(* 
    In the first equation, two expressions l and r to be unified have the same free head f, 
        a projectable sequence variable VAR$[SEQ0$[x]] appears under f, and 
        the expression in the opposite side has at least one argument t, which is not a sequence varible,
        but can be a sequence meta-variable.
    f != VAR$.
    A complete method of projection and widening applies. 
    Projection removes VAR$[SEQ0$[x]], replacing it with the empty sequence. 
    Widening replaces VAR$[SEQ0$[x]] with the sequence t,VAR$[SEQ0$[x]], if VAR$[SEQ0$[x]] does not occur in t.
*)
transform[ up[{{l:f_[VAR$[SEQ0$[x_]], args1___], r:f_[t_, args2___], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    Module[{subP = {VAR$[SEQ0$[x]] -> Sequence[]}, fresh, subW, upP, upW},
    	upP = up[{{f[args1]/.subP, r/.subP, widthCounter}, Sequence @@ ({equations}/.subP)}, lBoundVars, rBoundVars, renaming, term, compose[subst,subP]];
    	If[ FreeQ[ t, VAR$[SEQ0$[x]]],
    		fresh = Unique[ToString[x]];
    	    subW = {VAR$[SEQ0$[x]] -> Sequence[t, VAR$[SEQ0$[fresh]]]};
    	    upW = up[{{Drop[l/.subW,1], f[args2]/.subW, widthCounter+1}, Sequence @@ ({equations}/.subW)}, lBoundVars, rBoundVars, renaming, term, compose[subst,subW]];
    	    {upP, upW},
     	    	{upP}
    	]
    ]
transform[ up[{{l:f_[t_, args1___], r:f_[VAR$[SEQ0$[x_]], args2___], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    Module[{subP = {VAR$[SEQ0$[x]] -> Sequence[]}, fresh, subW, upP, upW},
        upP = up[{{l/.subP, f[args2]/.subP, widthCounter}, Sequence @@ ({equations}/.subP)}, lBoundVars, rBoundVars, renaming, term, compose[subst,subP]];
        If[ FreeQ[ t, VAR$[SEQ0$[x]]],
        	fresh = Unique[ToString[x]];
        	subW = {VAR$[SEQ0$[x]] -> Sequence[t, VAR$[SEQ0$[fresh]]]};
            upW = up[{{f[args1]/.subW, Drop[r/.subW,1], widthCounter+1}, Sequence @@ ({equations}/.subW)}, lBoundVars, rBoundVars, renaming, term, compose[subst,subW]];
            {upP, upW},
            	{upP}
        ]
    ]
(* 
    In the first equation, two expressions l and r to be unified have the same free head f, 
        a projectable sequence meta-variable META$[SEQ0$[x],l] appears under f, and 
        the expression in the opposite side has at least one argument t, which is neither a sequence varible
        not a sequence meta-variable.
    f != VAR$.
    A complete method of projection and widening applies. 
    Projection removes META$[SEQ0$[x],l], replacing it with the empty sequence. 
    Widening replaces META$[SEQ0$[x],l] with the sequence t,VAR$[SEQ0$[x],l], if VAR$[SEQ0$[x],l] does not occur in t
    and t does not contain arbitrary biut fixed constants, which do not appear in l.
*)
transform[ up[{{l:f_[META$[SEQ0$[x_], n_, fixedConstants_], args1___], r:f_[t_, args2___], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    Module[{subP = {META$[SEQ0$[x], n, fixedConstants] -> Sequence[]}, fresh, subW, upP, upW},
        upP = up[{{f[args1]/.subP, r/.subP, widthCounter}, Sequence @@ ({equations}/.subP)}, lBoundVars, rBoundVars, renaming, term, compose[subst,subP]];  
        If[ FreeQ[ t, META$[SEQ0$[x], n, fixedConstants]] && !containsExtraFixedConstant[ t, fixedConstants],
            fresh = Unique[ToString[x]];
            subW = {META$[SEQ0$[x], n, fixedConstants] -> Sequence[t, META$[SEQ0$[fresh], 0, fixedConstants]]};
            upW = up[{{Drop[l/.subW,1], f[args2]/.subW, widthCounter+1}, Sequence @@ ({equations}/.subW)}, lBoundVars, rBoundVars, renaming, term, compose[subst,subW]];
            {upP, upW},
                {upP}
        ]
    ]
transform[ up[{{l:f_[t_, args1___], r:f_[META$[SEQ0$[x_], n_, fixedConstants_], args2___], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    Module[{subP = {META$[SEQ0$[x], n, fixedConstants] -> Sequence[]}, fresh, subW, upP, upW},
        upP = up[{{l/.subP, f[args2]/.subP, widthCounter}, Sequence @@ ({equations}/.subP)}, lBoundVars, rBoundVars, renaming, term, compose[subst,subP]];
        If[ FreeQ[ t, META$[SEQ0$[x], n, fixedConstants]] && !containsExtraFixedConstant[ t, fixedConstants],
            fresh = Unique[ToString[x]];
            subW = {META$[SEQ0$[x], n, fixedConstants] -> Sequence[t, META$[SEQ0$[fresh], 0, fixedConstants]]};
            upW = up[{{f[args1]/.subW, Drop[r/.subW,1], widthCounter+1}, Sequence @@ ({equations}/.subW)}, lBoundVars, rBoundVars, renaming, term, compose[subst,subW]];
            {upP, upW},
                {upP}
        ]
    ]
(* 
    In the first equation, one expression has at least one argument, which is not a sequence variable, 
    and the expression in the opposite side has no arguments.
    The transformation fails. No new unification problems appear.
*)
transform[ up[{{ _[args__], _[], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] := {}
transform[ up[{{ _[], _[args__], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] := {}  

(*  
    The expressions to be unified are quantified with the same quantifer. 
    Conditions cond1 and cond2, and expressions expr1 and expr2 form new equations to be unified, module renaming of bound variables. 
    Bound variables in r2 should be a renamed copies of r1 (to guarantee alpha-equivalence).
    These variables will not appear in the unifier domains. They are put into the set of bound variables
    the transformation takes into account for renaming (lBoundVars and rBoundVars). 
    r1 and r2 also form a new unification problem, but they will be checked whether one is a renamed copy of another. 
*)
transform[ up[{{quant_[ r1_RNG$, cond1_, expr1_], quant_[ r2_RNG$, cond2_, expr2_], widthCounter_}, equations___}, 
       lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    Module[ {bv1, bv2, c = Unique["c"]}, 
        bv1 = DeleteDuplicates[ rngVariables[ r1]];
        bv2 = DeleteDuplicates[ rngVariables[ r2]];
        If[ Length[ bv1] =!= Length[ bv2], 
            {}, 
            	{up[{{cond1, cond2, widthCounter}, {expr1, expr2, widthCounter}, {c @@ r1, c @@ r2, widthCounter}, equations}, 
                    Union[ bv1, lBoundVars], Union[ bv2, rBoundVars], renaming, term, subst]}
        ]
    ]
    
(*  
    If the heads are symbols, then the rule fails, if they are distinct. Otherwise the expressions are decomposed.
    If the heads are compound expressions termselves, then they are added as a separate pair. In l and r, they are replaced with a new free symbol.   
*)
transform[ up[{{l:f_Symbol[args1___], r:g_Symbol[args2___], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], maxWidth_, _] :=
    If[f =!= g, 
    	{},
    	   decompose[ up[{{l, r, widthCounter}, equations}, lBoundVars, rBoundVars, renaming, term, subst]]]
transform[ up[{{t1_[args1___], t2_[args2___], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, _] :=
    With[ { f = Unique["f"]},
    	{up[ {{t1, t2, widthCounter}, {f[args1], f[args2], widthCounter}, equations}, lBoundVars, rBoundVars, renaming, term, subst]}]
    
(*  If none of the above rules apply, transformation returns the empty list  *)
transform[ up[{{_, _, _}, ___}, _, _, _, _, _], _, _] := {}


(*  Checking whether a term contains an arbitrary but fixed constant, which does not appear in the input list   *)
containsExtraFixedConstant[ term_, fixedConstantList_] := Complement[ Cases[ term, FIX$[_, _], {0, Infinity}, Heads -> True], fixedConstantList] =!= {}

(* 
   Decomposition of two expressions l and r with the same commutative head, marked by commutativeWrapper.
   r should be a renamed and, maybe, a permuted version of l.
   Currently not used.
*)
decompose[ up[{{l:c_[args1___], r:c_[args2___], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], _, commutativeWrapper[c_]] :=
   Module[ {a1, a2}, 
        a1 = Complement[{args1}, {args2}];
        a2 = Complement[{args2}, {args1}];
        If[ Length[ a1] =!= Length[ a2], 
        	{},
        	Map[up[Join[ #, {equations}], lBoundVars, rBoundVars, renaming, term, subst] &,
        		Map[ MapThread[ Append[ List[ #1, #2], widthCounter] &, {a1, #}] &, Permutations[a2]]]
        ]
    ]
    
(*  
    Decomposition of terms with the same commutative head involves replacing sequence variables with sequences of 
    term variables and then decomposing the obtained terms. The method is incomplete, as the length of sequences
    of term variables is bound by maxWidth.
    
    13.05.2014. TBD. To be adapted to meta-variables
*)    
decompose[ up[{{l:f_[args1___], r:f_[args2___], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_], maxWidth_, {commSymb1___, f_, commSymb2___}] :=
    Module[ {a1, a2, seqVariables, metaSeqVariables, replacingSubstritutions, seqVarReplacingSubstritutions, metaSeqVarReplacingSubstritutions, instances, decomposableInstances, decomposedInstances}, 
        a1 = Complement[{args1}, {args2}];
        a2 = Complement[{args2}, {args1}];
        seqVariables = Union[Cases[{args1,args2}, VAR$[SEQ0$[_]]]];
        metaSeqVariables = Union[Cases[{args1,args2}, META$[SEQ0$[_],_,_]]];
          (* Each seqVarReplacingSubstritution below has a form 
             { VAR$[SEQ0$[x]]->Sequence[VAR$[x1],...,VAR$[xn]], VAR$[SEQ0$[y]]->Sequence[VAR$[y1],...,VAR$[yk]],...} 
             where {VAR$[SEQ0$[x]], VAR$[SEQ0$[y]], ...} = seqVariables, n,k =< widthCounter, and
             x1,...,xn,y1,...,yk,... are fresh names. The goal is to replace each sequence variable under f
             with a sequence (whose length does not exceed widthCounter) of fresh term variables.  
          *)
        seqVarReplacingSubstritutions = 
            Distribute[ Map[Function[{x}, 
            	Map[Rule[x, Sequence @@ #] &, Table[Table[VAR$[Unique[ToString[x[[1, 1]]]]], {i, j}], {j, 0, maxWidth}]]], seqVariables], List];
          (* Each metaSeqVarReplacingSubstritution below has a form 
             { META$[SEQ0$[x],l1]->Sequence[META$[x1,l1],...,META$[xn,l1]], VAR$[SEQ0$[y],l2]->Sequence[META$[y1,l2],...,META$[yk,l2],...} 
             where {META$[SEQ0$[x],l1], META$[SEQ0$[y],l2], ...} = metaSeqVariables, n,k =< widthCounter, and
             x1,...,xn,y1,...,yk,... are fresh names. The goal is to replace each sequence meta-variable under f
             with a sequence (whose length does not exceed widthCounter) of fresh term meta-variables.  
          *)
        metaSeqVarReplacingSubstritutions = 
            Distribute[ Map[Function[{x}, 
                Map[Rule[x, Sequence @@ #] &, Table[Table[META$[Unique[ToString[x[[1, 1]]]], 0, x[[2]]], {i, j}], {j, 0, maxWidth}]]], metaSeqVariables], List];
        replacingSubstritutions = Outer[Join, seqVarReplacingSubstritutions, metaSeqVarReplacingSubstritutions, 1];  
        instances = Map[ {l/.#, r/.#}&, replacingSubstritutions];
        decomposableInstances = Select[instances, Length[#[[1]]] === Length[#[[2]]] &];
        decomposedInstances = Map[ Map[ Function[{x}, Append[x, widthCounter]], TransposeAnyHead [#[[1]], #[[2]]]]&, decomposableInstances];
        Map[ up[Join[ #, {equations}], lBoundVars, rBoundVars, renaming, term, compose[subst, replacingSubstritutions]] &, decomposedInstances]  
    ]
    
(*  
    Decomposition of two expressions l and r with the same free head. 
    If l and r have no arguments, they are removed. Otherwise, their prefixes until the first occurrence of a sequence variable are decomposed.
    The sequence variable should not be the first argument in either side. (This case should be captured by another transformation rule above.)
*)
decompose[ up[{{f_[], f_[], _}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_]] := 
	{up[{equations}, lBoundVars, rBoundVars, renaming, term, subst]}
decompose[ up[{{l:f_[args1___], r:f_[args2___], widthCounter_}, equations___}, lBoundVars_, rBoundVars_, renaming_, term_, subst_]] := 
	Module[ {l1, l2, minPrefix, decomposedPrefix, suffix1, suffix2, suffixEquation},
		l1 = LengthWhile[ {args1}, !MatchQ[#, (VAR$[SEQ0$[_]] | META$[SEQ0$[_], _, _])]&];
		l2 = LengthWhile[ {args2}, !MatchQ[#, (VAR$[SEQ0$[_]] | META$[SEQ0$[_], _, _])]&];
	    minPrefix = Min[ l1, l2];
	    If[ minPrefix === 0,
	    	{},
	    	  decomposedPrefix = Map[Append[#, widthCounter] &, Transpose[ {Take[ {args1}, minPrefix], Take[ {args2}, minPrefix]}]];
	    	  suffix1 = Drop[f[args1], minPrefix];
	    	  suffix2 = Drop[f[args2], minPrefix];
	    	  If[suffix1 === f[] && suffix2 === f[], suffixEquation = {}, suffixEquation = {{suffix1, suffix2, widthCounter}}];
	    	  {up[Join[decomposedPrefix, suffixEquation, {equations}], lBoundVars, rBoundVars, renaming, term, subst]}
	    ]
	]

(*  Composition of idempotent, domain-disjoint substitutions  *)
compose[subst1_, subst2_] := Join[subst1/.subst2, subst2]

(*  Restricting the domain of a substitution to a set of variables  *)
restrictSubstitutions[ substitutions_, vars_List] := Map[ restrictSubstitution[#, vars] &, substitutions]
restrictSubstitution[ substitution_, vars_List] := Select[ substitution, MemberQ[vars, #[[1]]] &]

(*  alphaRenaming[ expr, subst] renames all bound variables in expr uniquely, and returns the renamed version of expr
    together with the renaming substitution, composed with the restriction of subst to bound variables of expr. *)
alphaRenaming[quant_[r_RNG$, cond_, expr_], subst_] := 
    Module[ {boundVars, renaming, newSubst, condVariant, condBoundVars, exprVariant, exprBoundVars, renamedBoundVars}, 
    	boundVars = DeleteDuplicates[ rngVariables[ r]];
    	renaming = 
    	   Map[ Replace[#, 
    	       {Rule[VAR$[SEQ0$[x_]], Rule[#, VAR$[SEQ0$[Unique["bv"]]]]],
    	        Rule[VAR$[SEQ1$[x_]], Rule[#, VAR$[SEQ1$[Unique["bv"]]]]], 
    	        Rule[VAR$[x_?AtomQ], Rule[#, VAR$[Unique["bv"]]]]}] &, boundVars];
    	newSubst = Join[ renaming, Select[ subst, !MemberQ[ boundVars, First[#]] &]];
        {condVariant, condBoundVars} = alphaRenaming[cond, newSubst];
        {exprVariant, exprBoundVars} = alphaRenaming[expr, newSubst];
        renamedBoundVars = DeleteDuplicates[ Join[boundVars /. newSubst, condBoundVars, exprBoundVars]];
        {quant[ r /. newSubst, condVariant, exprVariant], renamedBoundVars}
    ]
alphaRenaming[VAR$[x_], subst_] := {(VAR$[x] /. subst), {}}
alphaRenaming[t_[args___], subst_] := 
    Module[{tVariant, tBoundVars, argumentVariantAndBoundVariables, listOfArgumentVariants, listOfBoundVariableLists}, 
    	{tVariant, tBoundVars} = alphaRenaming[t, subst];
    	argumentVariantAndBoundVariables = MapThread[List, Map[alphaRenaming[#, subst] &, {args}]];
        If[argumentVariantAndBoundVariables === {}, 
        	{listOfArgumentVariants, listOfBoundVariableLists} = {{},{{}}},
        		{listOfArgumentVariants, listOfBoundVariableLists} = argumentVariantAndBoundVariables
        ];
        {tVariant[Sequence @@ listOfArgumentVariants], DeleteDuplicates[Join @@ listOfBoundVariableLists]}
    ]
alphaRenaming[t_, _] := {t, {}}

(*  Extending Transpose from lists to expressions of any head. *)
TransposeAnyHead[f_[args1___], f_[args2___]] := Transpose[{{args1}, {args2}}]

End[] (* End Private Context *)

EndPackage[]