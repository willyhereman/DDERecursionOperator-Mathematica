
(* Last updated: June 3, 2010 by Hereman in Boulder *)

Print["Loading Package DDERecursionOperator.m of March 7, 2010."];

Integrability`DDERecursionOperator`print = PPrint;

oldContextPath = $ContextPath;

(* path taken out should be given in notebook *)
Get["InvariantsSymmetries.m"]; 

BeginPackage["Integrability`DDERecursionOperator`"];

$ContextPath = Flatten[
	              {
	               "Integrability`InvariantsSymmetries`",
	               "Integrability`InvariantsSymmetries`Private`",
                   "Assumptions`",
                   $ContextPath
                  }
               ];

DDERecursionOperator::usage =
  "DDERecursionOperator[eqn, u, {n, t}, opts] finds the recursion
operator of a differential difference equation for the function u.
  DDERecursionOperator[{eqn1, eqn2, ...}, {u1, u2, ...}, {n, t},
opts] finds the recursion operator of a system of differential
difference equations.";

GenerateSymmetries::usage = "";

InverseDifferenceDelta::usage = "";

Seed::usage = "";

HadToUseWeightedParameters::usage ="";

Format[InverseDifferenceDelta[expr_, {n_, t_}]] := Subsuperscript[\[EmptyUpTriangle], n, -1][expr, {n, t}]

Begin["`Private`"];

Options[DDERecursionOperator] = {HadToUseWeightedParameters -> False,
   WeightRules -> {}, MaxExplicitDependency -> 0, Seed -> 1,
   UndeterminedCoefficients -> C};

DDERecursionOperator[eqn_ /; ! ListQ[eqn], func_/; !ListQ[func], vars_List, opts___?OptionQ] :=
 DDERecursionOperator[{eqn}, {func}, vars, opts]

DDERecursionOperator[eqns_List, funcs_List, vars_List, opts___?OptionQ] /;
  (Length[eqns] == Length[funcs] && Length[vars] == 2 && (And @@ (MatchQ[#, _ == 0] & /@ eqns)) &&
    (And @@
      MapThread[(Count[#1[[1]],
            q_ /; MatchQ[q, Derivative[0, 1][#2][__]]] == 1 && Count[#1[[1]],
            q_ /; !FreeQ[q, Derivative[_, k_ /; k > 0][_][__]]] == 1)&, {eqns, funcs}]) &&
    IntegerQ[MaxExplicitDependency /. {opts} /. Options[DDERecursionOperator]]) :=
 Module[{sym, symrules, symmetries, rank, downshifts, upshifts, monomials, coef, coefindex = 1, i, j,
    r0, r1, discreteShift, function, inverseDifferenceDelta, r, rhs, FPrime, obstr, system, sys, solution},
  If[
   Length[sym = WeightRules /. {opts} /. Options[DDERecursionOperator]] == 0,
   sym = Quiet[
     Check[findWeights["DDE", eqns, funcs, vars, opts], $Failed,
      Weight::badchoice, Weight::nonuniform3]],
   sym = {sym, {}}
   ];
  (
    symrules = sym[[1]];
    Message[Weight::dilation, symrules];
    sym = filterWeights[funcs, vars, sym, opts];
    (
      coef =
       UndeterminedCoefficients /. {opts} /.
        Options[DDERecursionOperator];
      Integrability`DDERecursionOperator`print[
       "Calling \n ComputeNecessarySymmetries[", {eqns, funcs, vars,
        sym, Seed /. {opts} /. Options[DDERecursionOperator], opts},
       "]"];
      symmetries =
       ComputeNecessarySymmetries[eqns, funcs, vars, sym,
        Seed /. {opts} /. Options[DDERecursionOperator], opts];
      rank = Table[Last[#][[i]] - First[#][[j]], {i, Length[eqns]}, {j, Length[eqns]}]&[First /@ symmetries];
      Integrability`DDERecursionOperator`print[
       "Rank of the recursion operator is: ", rank];
      symmetries = Flatten[Last /@ symmetries, 1];
      Integrability`DDERecursionOperator`print[
       "Computed symmetries: \n", symmetries];
      Integrability`DDERecursionOperator`print[
       "Calling \n DifferenceInShifts[", {First[symmetries],
        Last[symmetries], funcs, vars[[1]]}, "]"];
      {downshifts, upshifts} = DifferenceInShifts[First[symmetries], Last[symmetries], funcs, vars[[1]]];
      Integrability`DDERecursionOperator`print[
       "{downshifts,upshifts}: ", {downshifts, upshifts}];
      symmetries =
       Union[Flatten[
         Transpose[
            Last[Normal[
              CoefficientArrays[#,
               Union[Cases[#, coef[_], -1]]]]]] & /@ symmetries, 1]];
      Integrability`DDERecursionOperator`print["Symmetries at pt. 2: ", symmetries];
      Integrability`DDERecursionOperator`print[
       "Calling \n FindMonomialsForR0[", {eqns, funcs, vars[[1]], sym[[1]], rank}, "]"];
      monomials = FindMonomialsForR0[eqns, funcs, vars[[1]], sym[[1]], rank];
      Integrability`DDERecursionOperator`print[
       "{monomials, upshifts, downshifts}: ", {monomials, upshifts, downshifts}];
      Integrability`DDERecursionOperator`print[
       "Calling \n FindPiecesForR1[", {eqns, funcs, vars, coef,
        symmetries, sym, rank, symrules, discreteShift, function},
       "]"];
      sym = FindPiecesForR1[eqns, funcs, vars, coef, symmetries, sym, rank,
         symrules, discreteShift, function];
      Integrability`DDERecursionOperator`print["sym after FindPiecesForR1: ", sym];
      (
        {symrules, symmetries} = sym;
        Integrability`DDERecursionOperator`print[
         "{symmetries, nonpolydensity} which will be used for R1 are: \n", {symmetries, symrules}];
        Integrability`DDERecursionOperator`print[
         "Calling \n BuildR0[", {monomials, upshifts, downshifts,
          vars[[1]], coef, coefindex, function, discreteShift, opts},
         "]"];
        {r0, coefindex} = BuildR0[monomials, upshifts, downshifts, vars[[1]], coef,
          coefindex, function, discreteShift, opts];
        Integrability`DDERecursionOperator`print["Candidate R0: \n", r0];
        Integrability`DDERecursionOperator`print[
         "Calling \n BuildR1[", {symmetries, symrules, vars, coef,
          coefindex, function, discreteShift, inverseDifferenceDelta},
          "]"];
        {r1, coefindex} = BuildR1[symmetries, symrules, vars, coef, coefindex,
          function, discreteShift, inverseDifferenceDelta];
        Integrability`DDERecursionOperator`print["Candidate R1: \n", r1];
        r = (r0+r1) /. {a_.*function[b_]+c_.*function[d_] :> function[a*b+c*d]};
        Integrability`DDERecursionOperator`print[" Candidate R: ", r];
        rhs = Last /@ Flatten[Solve[eqns, D[# @@ vars, vars[[2]]]& /@ funcs]];
        Integrability`DDERecursionOperator`print["F: \n", rhs];
        Integrability`DDERecursionOperator`print[
         "Calling \n FrechetDerivativeOperator[", {rhs, funcs, vars, discreteShift, function}, "]"];
        FPrime = FrechetDerivativeOperator[rhs, funcs, vars, discreteShift, function] /. function -> Function;
        Integrability`DDERecursionOperator`print["FPrime: \n", FPrime];
        Integrability`DDERecursionOperator`print[
         "Calling \n FrechetDerivativeOfR0InDirectionOfF[", {rhs, r0,
          funcs, vars, function, discreteShift}, "]"];
        obstr = FrechetDerivativeOfR0InDirectionOfF[rhs, r0, funcs, vars, function, discreteShift];
        Integrability`DDERecursionOperator`print["obstr at pt. 1: \n", obstr];
        (          
         Integrability`DDERecursionOperator`print[
           "Calling \n FrechetDerivativeOfR1InDirectionOfF[", {rhs,
            r1, funcs, vars, function, inverseDifferenceDelta}, "]"];
          obstr = obstr+FrechetDerivativeOfR1InDirectionOfF[rhs, r1, funcs, vars, function, inverseDifferenceDelta];
          Integrability`DDERecursionOperator`print["obstr at pt. 2: \n", obstr];
          (
           Integrability`DDERecursionOperator`print[
             "Calling \n CompositionOfOperators[", {r /.
               function -> Function, FPrime, function, discreteShift,
              inverseDifferenceDelta, vars[[1]], vars[[2]]}, "]"];            
            obstr = obstr+CompositionOfOperators[r /. function -> Function,
               FPrime, function, discreteShift,
               inverseDifferenceDelta, vars[[1]], vars[[2]]];            
            Integrability`DDERecursionOperator`print["obstr at pt. 3: \n", obstr];
            (              
              Integrability`DDERecursionOperator`print[
               "Calling \n CompositionOfOperators[", {FPrime,
                r /. function -> Function, function, discreteShift,
                inverseDifferenceDelta, vars[[1]], vars[[2]]}, "]"];
              obstr = obstr-CompositionOfOperators[FPrime,
                 r /. function -> Function, function, discreteShift,
                 inverseDifferenceDelta, vars[[1]], vars[[2]]];
              Integrability`DDERecursionOperator`print["obstr at pt. 4: \n", obstr];
              (                
                obstr = Flatten[obstr];
                Integrability`DDERecursionOperator`print["obstr at pt. 5: \n", obstr];
                system = {};
                Do[
                   sys = obstr[[i]] //. a_.*function[b_]+c_.*function[d_] :> function[a*b+c*d];
                Integrability`DDERecursionOperator`print["obstr at pt. 5: \n", sys];
                   sys = sys /. function[a_] :> function[Expand[a]];
                Integrability`DDERecursionOperator`print["obstr at pt. 6: \n", sys];
                   sys = sys /. function -> Identity;                
                   sys = sys /. {a_.*inverseDifferenceDelta[b_.*Slot[1], vars] :> 
                   	Together[a]*inverseDifferenceDelta[Together[b]*Slot[1], vars],
                   a_.*discreteShift[b_.*Slot[1], {vars[[1]], m_}] :>
                    Together[a]*discreteShift[b*Slot[1], {vars[[1]], m}]};
                Integrability`DDERecursionOperator`print["obstr at pt. 7: \n", sys];
                   sys = sys //.
                   {
                   a_.*discreteShift[Slot[1], {vars[[1]], m_}]+b_.*discreteShift[Slot[1], {vars[[1]], m_}] :>
                    Together[a+b]*discreteShift[Slot[1], {vars[[1]], m}],
                   a_.*Slot[1]+b_.*Slot[1] :> Together[a+b]*Slot[1],
                   a_.*inverseDifferenceDelta[b_.*Slot[1], vars] +
                    c_.*inverseDifferenceDelta[b_.*Slot[1], vars] :> 
                    Together[(a+c)]*inverseDifferenceDelta[b*Slot[1], vars],
                   a_.*inverseDifferenceDelta[b_.*Slot[1], vars]+
                    a_.*inverseDifferenceDelta[c_.*Slot[1], vars] :>
                    a*inverseDifferenceDelta[Together[(b+c)]*Slot[1], vars]
                   };
                Integrability`DDERecursionOperator`print[
                 "obstr at pt. 8: \n", sys];
                sys = sys //.
                  {
                   inverseDifferenceDelta[
                    a_*b_ /; FreeQ[a, Slot | vars[[1]] | vars[[2]]], vars] :> a*inverseDifferenceDelta[b, vars],
                   discreteShift[a_*b_ /; FreeQ[a, Slot | vars[[1]] | vars[[2]]], {vars[[1]], m_}] :>
                    a*discreteShift[b, {vars[[1]], m}],
                   inverseDifferenceDelta[0, vars] -> 0
                   };
                Integrability`DDERecursionOperator`print["obstr at pt. 9: \n", sys];
                 Integrability`DDERecursionOperator`print["i in Do: ", i];
                 sys = DSolve`DSolveMakeEquations[sys, vars];
                 Integrability`DDERecursionOperator`print["sys: ", sys];
                 Integrability`DDERecursionOperator`print[
                  "FreeQ[sys, False]: ", FreeQ[sys, False]];
                 system = {system, sys},
                 {i, Length[obstr]}
                 ];
                system = Flatten[system];                
                Integrability`DDERecursionOperator`print[
                 "system: \n", system];                
                solution =
                 Flatten[
                  Solve[system, Table[coef[i], {i, coefindex-1}]]];
                Integrability`DDERecursionOperator`print["solution: \n", solution];
                (
                 r = (r /. {a_.*function[b_] + c_.*function[d_] :> function[a*b+c*d]}) /. solution;
                 sym = Union[Cases[r, coef[_], -1]];
                 sym = {# -> 1, coef[_] -> 0}& /@ sym;
                 r = r /. sym;
                 (
                  (
                   (
                    r
                   ) /. NonCommutativeMultiply -> Times
                  ) /. function -> Function
                 ) /. {
                	  discreteShift -> DiscreteShift,
                      inverseDifferenceDelta -> InverseDifferenceDelta
                     }
                ) /; Length[solution] > 0
               ) /; FreeQ[obstr, $Failed]
              ) /; FreeQ[obstr, $Failed]
            ) /; FreeQ[obstr, $Failed]
          ) /; FreeQ[obstr, $Failed]
        ) /; sym =!= $Failed
      ) /; sym =!= Null
    ) /; sym =!= $Failed
  ]

BuildR0[monomials_, upshifts_, downshifts_, n_, coef_, index_, function_, discreteShift_, opts___] :=
 Module[{coefindex = index, r0, i, j, wpars},
  wpars = HadToUseWeightedParameters /. {opts} /. Options[DDERecursionOperator];
  r0 = Map[
    function,
    MapThread[
     Function[{a, b, c},
      If[c != 0, Sum[(Sum[coef[coefindex++]**a[[i]], {i, Length[a]}]+If[wpars, coef[coefindex++], 0])**
         discreteShift[#, {n, j}], {j, -1, c, -1}], 0] +
       (Sum[coef[coefindex++]**a[[i]], {i, Length[a]}]+If[wpars, coef[coefindex++], 0])**#+
       If[b != 0, Sum[(Sum[coef[coefindex++]**a[[i]], {i, Length[a]}]+If[wpars, coef[coefindex++], 0])**
         discreteShift[#, {n, j}], {j, b}], 0]
      ],
     {monomials, upshifts, downshifts},
     2
     ],
    {2}
    ];
  {r0, coefindex}
  ]

BuildR1[symmetries_, nonpolydensity_, vars_, coef_, index_, function_, discreteShift_, inverseDifferenceDelta_] :=
 Module[{coefindex = index, r1, i, j, k, nonpoly, sym},
  Integrability`DDERecursionOperator`print["symmetries in BuildR1: ",
   symmetries];
  Integrability`DDERecursionOperator`print["nonpolydensity in BuildR1: ", nonpolydensity];
  r1 = Table[0, {i, Length[First[symmetries]]}, {j, Length[First[nonpolydensity]]}];
  Do[
   sym = coef[coefindex]**# & /@ symmetries[[k]];
   coefindex++;
   (*sym=symmetries[[k]];*)
   nonpoly = nonpolydensity[[k]];
   r1 = r1 + Map[
      function,
      Outer[
       Function[{a, b}, If[PossibleZeroQ[b], 0, a**inverseDifferenceDelta[b**#, vars]]],
       sym, nonpoly],
      {2}
      ],
   {k, Length[symmetries]}
   ];
  {r1 //. {a_.*function[b_] + c_.*function[d_] :> function[a*b + c*d]}, coefindex}
  ]

ComputeNecessarySymmetries[eqns_, funcs_, vars_, sym_, n_, opts___] :=
 Module[{symmetries = {}, i = 0},
  Integrability`DDERecursionOperator`print[
   "in ComputeNecessarySymmetries"];
      While[
   Length[symmetries] < n + 1,
         i++;
         symmetries = 
            Union[
                symmetries,
                Internal`DeactivateMessages[
                   {#, ddeSymmetry[
                             eqns, funcs, vars, sym, #,
                            opts]
                       } & /@ trialSymRanks[funcs, vars, sym[[1]], trialRanks[{i-1, i}, sym[[1]]]],
                   Solve::svars
                 ]
              ] /. {{{(_? NumericQ) ..}, {{(0) ..}}} :>
       Sequence[], {{(_?NumericQ) ..}, {{q__} /; (And @@ (FreeQ[{q}, #] & /@ funcs))}} :> Sequence[]};
       ];
  Integrability`DDERecursionOperator`print["Exiting ComputeNecessarySymmetries"];
  symmetries
  ]

ComputeNecessaryDensities[eqns_, funcs_, vars_, coef_, sym_, opts___] :=
 Module[{densities = {}, i = 0},
  Integrability`DDERecursionOperator`print[
   "in ComputeNecessaryDensities"];
      While[
   Length[densities] < 1 && i < 9,
         i++;
         densities =
            Union[
                densities,
                Internal`DeactivateMessages[
                   {#, ddeDensity[
                             eqns, funcs, vars, sym, #,
                            opts]
                       } & /@
                            trialRanks[
                               {i - 1, i}, sym[[1]]
                             ],
                   Solve::svars
                 ]
              ] /. {{(_? NumericQ) , {{(0) ..}}} :>
                    Sequence[], {(_?NumericQ), {{q__} /; (And @@ (FreeQ[{q}, #] & /@ funcs))}} :> Sequence[]}
       ];
  Integrability`DDERecursionOperator`print["densities in ComputeNecessaryDensities-1: ", densities];
  densities = Flatten[Last /@ densities];
  densities = Union[Flatten[Last[Normal[
      CoefficientArrays[#, Union[Cases[#, coef[_], -1]]]]] & /@ densities, 1]];
  Integrability`DDERecursionOperator`print["densities in ComputeNecessaryDensities-2: ", densities];
  Integrability`DDERecursionOperator`print["Exiting ComputeNecessaryDensities"];
  densities
  ]

DifferenceInShifts[sym1_, sym2_, funcs_, n_] :=
 Module[{monomials, downshifts, upshifts, i, j},
  Integrability`DDERecursionOperator`print["in DifferenceInShifts"];
  Integrability`DDERecursionOperator`print["sym1: ", sym1];
  Integrability`DDERecursionOperator`print["sym2: ", sym2];
  monomials =
   Map[Union[rootMonomialList[#, funcs]] &, {sym1, sym2}, {2}];
  Integrability`DDERecursionOperator`print["monomials: ", monomials];
  upshifts = monomials /. (q_[n + p_., _] /; MemberQ[funcs, q]) :> p;
  Integrability`DDERecursionOperator`print["upshifts-1: ", upshifts];
  downshifts = Map[Select[#, Negative] &, upshifts, {2}];
  Integrability`DDERecursionOperator`print["downshifts-1: ",
   downshifts];
  upshifts = Map[Select[#, Positive] &, upshifts, {2}];
  Integrability`DDERecursionOperator`print["upshifts-2: ", upshifts];
  upshifts = Map[Max[0, #] &, upshifts, {2}];
  Integrability`DDERecursionOperator`print["upshifts-3: ", upshifts];
  downshifts = Map[Min[0, #] &, downshifts, {2}];
  Integrability`DDERecursionOperator`print["downshifts-2: ", downshifts];
  upshifts = Table[upshifts[[2, i]] - upshifts[[1, j]], {i, Length[upshifts[[2]]]}, {j, Length[upshifts[[1]]]}];
  Integrability`DDERecursionOperator`print["upshifts-4: ", upshifts];
  downshifts = Table[downshifts[[2, i]] - downshifts[[1, j]], 
  	             {i, Length[downshifts[[2]]]}, {j, Length[downshifts[[1]]]}];
  Integrability`DDERecursionOperator`print["downshifts-3: ", downshifts];
  Integrability`DDERecursionOperator`print["Exiting DifferenceInShifts"];
  {downshifts, upshifts}
  ]

FindMonomialsForR0[eqns_, funcs_, n_, weights_, rank_] :=
 Module[{monomials, weightrules},
  Integrability`DDERecursionOperator`print["in FindMonomialsForR0"];
  monomials =
   Union[Flatten[
     DeleteCases[
      Map[rootMonomialList[#, funcs] &, (Part[#, 1] & /@ eqns)],
      Derivative[0, 1][_][__], -1]]];
  Integrability`DDERecursionOperator`print["monomials-1: ", monomials];
  weightrules = weights /. {(u_[n, t_] /; MemberQ[funcs, u]), b_} :>  (u[n + p_., t] -> b);
  Integrability`DDERecursionOperator`print["weightrules-1: ", weightrules];
  monomials = monomials /. (u_[n + p_., t_] /; MemberQ[funcs, u]) :> {u[n + p, t], u[n + p, t] /. weightrules};
  Integrability`DDERecursionOperator`print["monomials-2: ", monomials];
  monomials = Map[findFormWithDesiredRank[#, monomials] &, rank, {2}];
  Integrability`DDERecursionOperator`print["monomials-3: ", monomials];
  Integrability`DDERecursionOperator`print["Exiting FindMonomialsForR0"];
  monomials
  ]

findFormWithDesiredRank[rank_, monomials_] :=
 Module[{auxfunc, i},
  auxfunc[e1_, e2_] :=
   Flatten[Table[{#[[1]]*e2[[1]]^i, #[[2]] + i*e2[[2]]}, {i, 0, Floor[(rank - #[[2]])/e2[[2]]]}] & /@ e1, 1];
  First /@ Select[Fold[auxfunc, {{1, 0}}, monomials], #[[2]] == rank &]
  ]

FindNonPolynomialDensityByTrial[eqns_, funcs_, vars_, coef_] :=
 Module[{i, j = Length[funcs]},
  DeleteCases[
   Flatten[
    ddedensity[eqns, funcs, vars, #] & /@
     Flatten[{Table[
        coef[1]*Log[funcs[[i]][Sequence @@ vars]], {i, j}],
       Table[coef[1]/funcs[[i]][Sequence @@ vars], {i, j}],
       (*coef[1]*Log[Product[funcs[[i]][Sequence @@ vars], {i, j}]],*)
       coef[1]*Log[1+Product[funcs[[i]][Sequence @@ vars], {i, j}]]}
      ]
    ],
   x_0
   ]
  ]

FindPiecesForR1[eqns_, funcs_, vars_, coef_, symmetries_, weights_,
  rank_, rules_, discreteShift_, function_, opts___] :=
 Module[{nonpolydensity, sym, symrules},
  Integrability`DDERecursionOperator`print["in FindPiecesForR1"];
  nonpolydensity = FindNonPolynomialDensityByTrial[eqns, funcs, vars, coef] /. coef[1] -> 1;
  Integrability`DDERecursionOperator`print["nonpolydensity-1: ", nonpolydensity];
  Integrability`DDERecursionOperator`print["found density: ",
  	ComputeNecessaryDensities[eqns, funcs, vars, coef, weights, opts]];
  nonpolydensity = Flatten[{nonpolydensity, ComputeNecessaryDensities[eqns, funcs, vars, coef, weights, opts]}];
  Integrability`DDERecursionOperator`print["nonpolydensity-2: ", nonpolydensity];
  (
    (*nonpolydensity=Outer[D[#1,#2]&,nonpolydensity,(#@@vars&) /@ funcs];*)
    nonpolydensity = (Function[{a},
         frechetDerivativeOperator[a, #, vars[[1]], discreteShift,
            function] & /@ funcs] /@ (nonpolydensity /.
          p_[a_, vars[[2]]] /; MemberQ[funcs, p] :>
           p[a])) /. {function ->
        Identity, (p_)[a_] /; MemberQ[funcs, p] -> p[a, vars[[2]]]};
    Integrability`DDERecursionOperator`print[
     "derivative of nonpolydensity-3: ", nonpolydensity];
    nonpolydensity = nonpolydensity /. {(a_:1)**discreteShift[Slot[1], {vars[[1]], k_}] :>
         DiscreteShift[a, {vars[[1]], -k}], Slot[1] -> 1} /. NonCommutativeMultiply -> Times;
    Integrability`DDERecursionOperator`print[
     "derivative of nonpolydensity after replacement rules: ", nonpolydensity];
    (*sym=Flatten[Outer[Times,#,nonpolydensity],1]& /@ symmetries;*)
    sym = (Outer[Times, symmetries, #] & /@ nonpolydensity) /. NonCommutativeMultiply -> Times;
    Integrability`DDERecursionOperator`print["sym-3: ", sym];
    symrules = rules /. {(Weight[a_ /; MemberQ[vars, a]] -> b_) :> Sequence[],
       Weight[a_ /; MemberQ[funcs, a]] :> Weight[a @@ vars]};
    Integrability`DDERecursionOperator`print["symrules-1: ", symrules];
    symrules =
     ((sym /. (a_?(And[Not[ListQ[#]], # =!= List] &)) :> Weight[a]) //.
        {
         Weight[{a_, b___}] :> {Weight[a], Weight[{b}]},
         Weight[a_ + b___] :> Max[{Weight[a], Weight[{b}]}],
         Weight[a_*b_] :> Weight[a] + Weight[b],
         Weight[Times[a_., Power[b_, -1]]] :> Weight[a] - Weight[b],
         Weight[(a_ /; (And @@ (FreeQ[a, #] & /@ funcs)) &&
               (And @@ (FreeQ[a, #] & /@ vars)))+b_] :> Weight[b],
         Weight[a_ /; (And @@ (FreeQ[a, #] & /@ funcs)) &&
             (And @@ (FreeQ[a, #] & /@ vars))] -> 0,
         Weight[u_[vars[[1]] + p_., vars[[2]]]^r_. /;
            MemberQ[funcs, u]] :>  r*Weight[u[vars[[1]], vars[[2]]]]
         }) /. symrules;
    Integrability`DDERecursionOperator`print["symrules-2: ", symrules];
    symrules = Position[Map[Min, Map[rank - # &, symrules, {2}], {2}], 0];
    (*symrules=Flatten[Position[symrules,#]& /@ Select[symrules,Min[rank-#]>= 0&]];*)
    Integrability`DDERecursionOperator`print["symrules-3: ", symrules];
    (*sym=Take[symmetries,symrules];*)
    sym = Apply[{nonpolydensity[[#1]], symmetries[[#2]]} &, symrules, {1}];
    Integrability`DDERecursionOperator`print["sym-5: ", sym];
    Integrability`DDERecursionOperator`print["exiting FindPiecesForR1"];
    (*{Flatten[sym],nonpolydensity}*)
    Transpose[sym]
    ) /; Length[nonpolydensity] > 0
  ]

FindPiecesForR1[___] := $Failed

ddedensity[eqns_, funcs_, vars_, density_] :=
 Module[{rhsEqn, obstr, system},
  Integrability`DDERecursionOperator`print["in ddedensity"];
  Integrability`DDERecursionOperator`print["trial density: ", density];
  rhsEqn[i_, m_] :=
   Flatten[Solve[eqns[[i]],
       D[funcs[[i]][Sequence @@ vars], vars[[2]]]]][[1, 2]] /.
    vars[[1]] -> m;
  obstr =
   D[density,
     vars[[2]]] /. (Derivative[0, 1][f_][m_, vars[[2]]] :>
      rhsEqn[Flatten[Position[funcs, f]][[1]], m]);
  Integrability`DDERecursionOperator`print["obstr-1: ", obstr];
  obstr = Simplify[shiftmonomial[ExpandAll[obstr], funcs, vars]];
  Integrability`DDERecursionOperator`print["obstr-2: ", obstr];
  If[Length[obstr] == 0, Return[{{density}}]];
  system = Union[buildEquationList[obstr, funcs, vars]];
  Integrability`DDERecursionOperator`print["system: ", system];
  Integrability`DDERecursionOperator`print[
   "exiting ddedensity-calling analyzeSystem"];
  analyzeSystem[eqns, vars, {density}, system]
  ]

shiftmonomial[expr_, funcs_, vars_] /; (And @@ (FreeQ[expr, #] & /@ funcs)) := expr

shiftmonomial[expr_Plus , funcs_, vars_] := shiftmonomial[#, funcs, vars]& /@ expr

shiftmonomial[expr_, funcs_, vars_] :=
Block[{i = Min[Cases[{expr}, x_[vars[[1]]+q_., vars[[2]]] /; MemberQ[funcs, x] :> q, -1]]},
	expr /. (vars[[1]] -> vars[[1]]-i)]

FrechetDerivativeOperator[rhs_, funcs_, vars_, discreteShift_, function_] :=
 Module[{res, length = Length[funcs]},
  res = Catch[
    MapThread[
     frechetDerivativeOperator[#1 /.
        p_[a_, vars[[2]]] /; MemberQ[funcs, p] :>  p[a], #2,
       vars[[1]], discreteShift, function] &,
     {Flatten[Transpose[Table[rhs, {length}]]], Flatten[Table[funcs, {length}]]}]];
  Partition[res /. (p_)[a_] /; MemberQ[funcs, p] -> p[a, vars[[2]]], length] /; res =!= $Failed
  ]

FrechetDerivativeOperator[___] := $Failed

frechetDerivativeOperator[F_, u_, n_, discreteShift_, function_] /; FreeQ[F, u] := function[0]

frechetDerivativeOperator[F_, u_, n_, discreteShift_, function_] :=
Module[{shifts},
  Integrability`DDERecursionOperator`print["F in frechetDerivativeOperator: ", F];
  Integrability`DDERecursionOperator`print["u in frechetDerivativeOperator: ", u];
  Integrability`DDERecursionOperator`print["n in frechetDerivativeOperator: ", n];
  shifts = FindShifts[F, u, n];
  Integrability`DDERecursionOperator`print["shifts in frechetDerivativeOperator: ", shifts];
  (
    function[
     Total[(D[F, u[n + #]]**discreteShift[_, {n, #}]& /@ shifts) /. {discreteShift[_, {n, 0}] -> #,
        discreteShift[_, {n, m_}] -> discreteShift[#, {n, m}]}]]
    ) /; shifts =!= $Failed
  ]

frechetDerivativeOperator[___] := Throw[$Failed]

CompositionOfOperators[r_, fprime_, function_, discreteShift_, inverseDifferenceDelta_, n_, t_] :=
 Module[{res},
  Integrability`DDERecursionOperator`print["r in compositionOfOperators: ", r];
  Integrability`DDERecursionOperator`print["fprime in compositionOfOperators: ", fprime];
  (*res=Inner[#1@#2&,r,fprime,Plus];*)
  res = Inner[Function[{a, b}, Composition[a, b][#]], r, fprime, Plus];
  (*res=res/.Function->Identity;*)
  Integrability`DDERecursionOperator`print["res in CompositionOfOperators: ", res];
  res = res //. {
     discreteShift[(a_: 1) ** discreteShift[Slot[1], {n, k_}] +
        b_, {n, l_}] :>
      discreteShift[a ** discreteShift[Slot[1], {n, k}], {n, l}] +
       discreteShift[b, {n, l}],
     discreteShift[(a_: 1) ** Slot[1] + b_, {n, k_}] :>
      discreteShift[a ** Slot[1], {n, k}] + discreteShift[b, {n, k}],
     discreteShift[(a_: 1) **
         inverseDifferenceDelta[(b_: 1) ** Slot[1], {n, t}] + c_, {n,
        k_}] :> discreteShift[
        a ** inverseDifferenceDelta[b ** Slot[1], {n, t}], {n, k}] +
       discreteShift[c, {n, k}],
       inverseDifferenceDelta[(a_: 1) ** ((b_: 1) **
           discreteShift[Slot[1], {n, k_}] + c_), {n, t}] :>
      inverseDifferenceDelta[
        Together[a*b] ** discreteShift[Slot[1], {n, k}], {n, t}] +
       inverseDifferenceDelta[a ** c, {n, t}],     
     inverseDifferenceDelta[
       a_ ** b_ ** discreteShift[Slot[1], {n, k_}], {n, t}] :>
      inverseDifferenceDelta[
       Together[a*b] ** discreteShift[Slot[1], {n, k}], {n, t}],
     inverseDifferenceDelta[(a_: 1) ** ((b_: 1) ** Slot[1] + c_), {n,
        t}] :> inverseDifferenceDelta[
        Together[a*b] ** Slot[1], {n, t}] +
       inverseDifferenceDelta[a ** c, {n, t}],
     inverseDifferenceDelta[a_ ** b_ ** Slot[1], {n, t}] :>
      inverseDifferenceDelta[Together[a*b] ** Slot[1], {n, t}],     
     a_ ** ((b_: 1) ** discreteShift[Slot[1], {n, k_}] + c_) /;
       FreeQ[{a, b}, Slot] :>
      Together[a*b] ** discreteShift[Slot[1], {n, k}] + a ** c,
     a_ ** b_ ** discreteShift[Slot[1], {n, k_}] /;
       FreeQ[{a, b}, Slot] :>
      Together[a*b] ** discreteShift[Slot[1], {n, k}],
     a_ ** ((b_: 1) ** Slot[1] + c_) /; FreeQ[{a, b}, Slot] :>
      Together[a*b] ** Slot[1] + a ** c,
     a_ ** b_ ** Slot[1] /; FreeQ[{a, b}, Slot] :>
      Together[a*b] ** Slot[1],
     a_ ** ((b_: 1) **
           inverseDifferenceDelta[(c_: 1) ** Slot[1], {n, t}] + d_) /;
        FreeQ[{a, b}, Slot] :>
      Together[a*b] ** inverseDifferenceDelta[c ** Slot[1], {n, t}] +
       a ** d,
     a_ ** b_ ** inverseDifferenceDelta[(c_: 1) ** Slot[1], {n, t}] /;
        FreeQ[{a, b}, Slot] :>
      Together[a*b] ** inverseDifferenceDelta[c ** Slot[1], {n, t}]
     };
  res = res //. {
     discreteShift[(a_: 1) ** discreteShift[b_, {n, m_}], {n, l_}] :>
      discreteShift[a, {n, l}] ** discreteShift[b, {n, l + m}],
     discreteShift[a_ ** b_, c_] :>
      discreteShift[a, c] ** discreteShift[b, c],
     inverseDifferenceDelta[(a_: 1) **
        discreteShift[Slot[1], {n, k_ /; k < 0}], {n,
        t}] :> -a ** discreteShift[Slot[1], {n, k}] +
       inverseDifferenceDelta[
        discreteShift[a, {n, 1}] **
         discreteShift[Slot[1], {n, k + 1}], {n, t}],
     inverseDifferenceDelta[(a_: 1) **
        discreteShift[Slot[1], {n, k_ /; k > 0}], {n, t}] :>
      discreteShift[a, {n, -1}] **
        discreteShift[Slot[1], {n, k - 1}] +
       inverseDifferenceDelta[
        discreteShift[a, {n, -1}] **
         discreteShift[Slot[1], {n, k - 1}], {n, t}],
     discreteShift[(a_: 1) **
        inverseDifferenceDelta[(b_: 1) ** Slot[1], {n, t}], {n,
        k_ /; k < 0}] :> -discreteShift[a, {n, k}] **
         discreteShift[b, {n, k}] ** discreteShift[Slot[1], {n, k}] +
       discreteShift[
        discreteShift[a, {n, -1}] **
         inverseDifferenceDelta[b ** Slot[1], {n, t}], {n, k + 1}],
     discreteShift[(a_: 1) **
        inverseDifferenceDelta[(b_: 1) ** Slot[1], {n, t}], {n,
        k_ /; k > 0}] :>
      discreteShift[a, {n, k}] ** discreteShift[b, {n, k - 1}] **
        discreteShift[Slot[1], {n, k - 1}] +
       discreteShift[
        discreteShift[a, {n, 1}] **
         inverseDifferenceDelta[b ** Slot[1], {n, t}], {n, k - 1}],
     1 ** a_ :>  a,
     a_ ** 1 :>  a,
     discreteShift[a_, {n, 0}] :> a,
     discreteShift[a_ /; FreeQ[a, Slot | n | t], b_] :> a
     };
  res = res /. NonCommutativeMultiply -> Times;
  res = Expand[
    res /. {discreteShift[a_ /; FreeQ[a, Slot], b_] :>
       DiscreteShift[a, b],
      inverseDifferenceDelta[a_ /; FreeQ[a, Slot], b_] :>
       InverseDifferenceDelta[a, b]}];
  res = res /. {a_.*inverseDifferenceDelta[b_.*Slot[1], {n, t}] :>
      Together[a]*inverseDifferenceDelta[Together[b]*Slot[1], {n, t}],
     a_.*discreteShift[b_.*Slot[1], {n, k_}] :>
      Together[a]*discreteShift[b*Slot[1], {n, k}]};
  res = res //.
    {
     a_.*discreteShift[Slot[1], {n, k_}] +
       b_.*discreteShift[Slot[1], {n, k_}] :>
      Together[a + b]*discreteShift[Slot[1], {n, k}],
     a_.*Slot[1] + b_.*Slot[1] :> Together[a + b]*Slot[1],
     a_.*inverseDifferenceDelta[b_.*Slot[1], {n, t}] +
       c_.*inverseDifferenceDelta[b_.*Slot[1], {n, t}] :>
      Together[(a + c)]*inverseDifferenceDelta[b*Slot[1], {n, t}],
     a_.*inverseDifferenceDelta[b_.*Slot[1], {n, t}] +
       a_.*inverseDifferenceDelta[c_.*Slot[1], {n, t}] :>
      a*inverseDifferenceDelta[Together[(b + c)]*Slot[1], {n, t}]
     };
  res = res //. {
     inverseDifferenceDelta[
       a_*b_ /; FreeQ[a, Slot | n | t], {n, t}] :>
      a*inverseDifferenceDelta[b, {n, t}],
     discreteShift[a_*b_ /; FreeQ[a, Slot | n | t], {n, m_}] :>
      a*discreteShift[b, {n, m}],
      inverseDifferenceDelta[0, {n, t}] -> 0
     };
  Map[function, res, {2}]
  ]

FrechetDerivativeOfR0InDirectionOfF[F_, R0_, funcs_, vars_, function_,
   discreteShift_] :=
 Module[{rule, res},
  rule = p_[a_, vars[[2]]] /; MemberQ[funcs, p] :>  p[a];
  res = Catch[
    Map[frechetDerivativeOfR0InDirectionOfF[F /. rule, #, funcs,
       vars[[1]], function] &, (R0 /. function -> Function) /.
      rule, {2}]];
  res = (res //. {a_.*function[b_] + c_.*function[d_] :>
        function[a*b + c*d]}) /. function[a_] :> function[Expand[a]];
  res = res //.
    {
     a_.*discreteShift[Slot[1], {vars[[1]], k_}] +
       b_.*discreteShift[Slot[1], {vars[[1]], k_}] :>
      Together[a + b]*discreteShift[Slot[1], {vars[[1]], k}],
     a_.*Slot[1] + b_.*Slot[1] :> Together[a + b]*Slot[1]
     };
  Integrability`DDERecursionOperator`print["res: ", res];
  (res /. (p_)[a_] /; MemberQ[funcs, p] -> p[a, vars[[2]]] ) /;
   res =!= $Failed
  ]

FrechetDerivativeOfR0InDirectionOfF[___] := $Failed

frechetDerivativeOfR0InDirectionOfF[F_, R0_, funcs_, n_, function_] :=
 Total[MapThread[frechetderivativeOfR0InDirectionOfF[#1, R0, #2, n, function] &, {F, funcs}]]

frechetderivativeOfR0InDirectionOfF[F_, R0_, u_, n_, function_] :=
 Module[{r0, shifts},
  Integrability`DDERecursionOperator`print[
   "F in frechetderivativeOfR0InDirectionOfF: ", F];
  Integrability`DDERecursionOperator`print[
   "R0 in frechetderivativeOfR0InDirectionOfF: ", R0];
  Integrability`DDERecursionOperator`print[
   "u in frechetderivativeOfR0InDirectionOfF: ", u];
  Integrability`DDERecursionOperator`print[
   "n in frechetderivativeOfR0InDirectionOfF: ", n];
  r0 = R0 /. {NonCommutativeMultiply -> Times, Function -> Identity};
  Integrability`DDERecursionOperator`print[
   "r0 in frechetderivativeOfR0InDirectionOfF: ", r0];
  shifts = If[FreeQ[r0, u], {0}, FindShifts[r0, u, n]];
  Integrability`DDERecursionOperator`print[
   "shifts in frechetderivativeOfR0InDirectionOfF: ", shifts];
  (
    function[
     Total[(DiscreteShift[F, {n, #}]*D[r0, u[n + #]] & /@ shifts)]]
    ) /; shifts =!= $Failed
  ]

frechetderivativeOfR0InDirectionOfF[___] := Throw[$Failed]

FrechetDerivativeOfR1InDirectionOfF[F_, R1_, funcs_, vars_, function_,
   inverseDifferenceDelta_] :=
 Module[{rule, res},
  rule = p_[a_, vars[[2]]] /; MemberQ[funcs, p] :>  p[a];
  res = Catch[
    Map[frechetDerivativeOfR1InDirectionOfF[F /. rule, #, funcs, vars,
       function,
       inverseDifferenceDelta] &, (R1 /. function -> Function) /.
      rule, {2}]];
  res = (res //. {a_.*function[b_] + c_.*function[d_] :>
        function[a*b + c*d]}) /. function[a_] :> function[Expand[a]];
  res = res /. {a_.*inverseDifferenceDelta[b_.*Slot[1], vars] :>
      Together[a]*inverseDifferenceDelta[Together[b]*Slot[1], vars]};
  res = res //.
    {
     a_.*inverseDifferenceDelta[b_.*Slot[1], vars] +
       c_.*inverseDifferenceDelta[b_.*Slot[1], vars] :>
      Together[(a + c)]*inverseDifferenceDelta[b*Slot[1], vars],
     a_.*inverseDifferenceDelta[b_.*Slot[1], vars] +
       a_.*inverseDifferenceDelta[c_.*Slot[1], vars] :>
      a*inverseDifferenceDelta[Together[(b + c)]*Slot[1], vars]
     };
  Integrability`DDERecursionOperator`print[
   "res in FrechetDerivativeOfR1InDirectionOfF: ", res];
  (res /. (p_)[a_] /; MemberQ[funcs, p] -> p[a, vars[[2]]] ) /;
   res =!= $Failed
  ]

FrechetDerivativeOfR1InDirectionOfF[___] := $Failed

frechetDerivativeOfR1InDirectionOfF[F_, R1_, funcs_, vars_, function_,
   inverseDifferenceDelta_] :=
 Total[MapThread[frechetderivativeOfR1InDirectionOfF[#1, R1, #2, vars, function,
 	inverseDifferenceDelta] &, {F, funcs}]]

frechetderivativeOfR1InDirectionOfF[F_, R1_, u_, vars_, function_, inverseDifferenceDelta_] :=
 Module[{r1, f},
  Integrability`DDERecursionOperator`print[
   "F in frechetDerivativeOfR1InDirectionOfF: ", F];
  Integrability`DDERecursionOperator`print[
   "R1 in frechetDerivativeOfR1InDirectionOfF: ", R1];
  r1 = R1 /. {NonCommutativeMultiply -> Times, Function -> Identity,
     Slot[1] -> 1};
  Integrability`DDERecursionOperator`print[
   "r1 in frechetDerivativeOfR1InDirectionOfF: ", r1];
  (Thread[f[F, r1, u, vars, function, inverseDifferenceDelta],
      Plus, {2}] /.
     f -> frechetderivativeofr1indirectionoff) //. {a_.*function[b_] +
       c_.*function[d_] :> function[a*b + c*d]}
  ]

frechetderivativeofr1indirectionoff[F_, R1_, u_, vars_, function_, inverseDifferenceDelta_] :=
 Module[{U, V, shifts, res},
  U = R1 /. inverseDifferenceDelta[_, _] -> 1;
  V = Cases[R1, inverseDifferenceDelta[a_, _] :> a , -1];
  V = If[Length[V] == 0, 0, V[[1]]];
  shifts = If[FreeQ[U, u], {0}, FindShifts[U, u, vars[[1]]]];
  Integrability`DDERecursionOperator`print["shifts-1: ", shifts];
  (
    res = Total[(DiscreteShift[F, {vars[[1]], #}]*
           D[U, u[vars[[1]] + #]] &) /@ shifts]*
      inverseDifferenceDelta[V*#, vars];
    shifts = If[FreeQ[V, u], {0}, FindShifts[V, u, vars[[1]]]];
    Integrability`DDERecursionOperator`print["shifts-2: ", shifts];
    (
      res = res +
        Total[
         Function[{k},
           U*inverseDifferenceDelta[
             DiscreteShift[F, {vars[[1]], k}]*
              D[V, u[vars[[1]] + k]]*#, vars]] /@ shifts];
      res =
       res /. {a_.*inverseDifferenceDelta[b_.*Slot[1], vars] :>
          Together[a]*
           inverseDifferenceDelta[Together[b]*Slot[1], vars]};
      res = res //.
        {
         a_.*inverseDifferenceDelta[b_.*Slot[1], vars] +
           c_.*inverseDifferenceDelta[b_.*Slot[1], vars] :>
          Together[(a + c)]*inverseDifferenceDelta[b*Slot[1], vars],
         a_.*inverseDifferenceDelta[b_.*Slot[1], vars] +
           a_.*inverseDifferenceDelta[c_.*Slot[1], vars] :>
          a*inverseDifferenceDelta[Together[(b + c)]*Slot[1], vars],
         inverseDifferenceDelta[0, vars] -> 0
         };
      (*res=res/.{a_.*inverseDifferenceDelta[b_.*Slot[1],vars]:>
      Together[a]*inverseDifferenceDelta[Together[b]*Slot[1],vars]};*)
      function[res]
      ) /; shifts =!= $Failed
    ) /; shifts =!= $Failed
  ]

frechetderivativeofr1indirectionoff[___] := Throw[$Failed]

(********************************************************************************************************************)

GenerateSymmetries[R_, startingsymmetry_, n_] :=
   Catch[Rest[NestList[GenerateNextSymmetry[R, #] &, startingsymmetry, n]]]

GenerateNextSymmetry[R_, startingsymmetry_] :=
 Module[{inverseDifferenceDelta, next},
  next = Inner[#1@#2 &, 
    R /. InverseDifferenceDelta -> inverseDifferenceDelta, 
    startingsymmetry, Plus];
  next = next /. {a_.*inverseDifferenceDelta[b_, {n, t}] :> 
      Together[a]*inverseDifferenceDelta[Together[b], {n, t}]};
  next = next //. {a_.*inverseDifferenceDelta[b_, {n, t}] + 
       c_.*inverseDifferenceDelta[b_, {n, t}] :> 
      Together[(a + c)]*inverseDifferenceDelta[b, {n, t}], 
     a_.*inverseDifferenceDelta[b_, {n, t}] + 
       a_.*inverseDifferenceDelta[c_, {n, t}] :> 
      a*inverseDifferenceDelta[Together[(b + c)], {n, t}]};
  next = next //. {inverseDifferenceDelta[
       a_*b_ /; FreeQ[a, n | t], {n, t}] :> 
      a*inverseDifferenceDelta[b, {n, t}], 
     inverseDifferenceDelta[0, {n, t}] -> 0};
  next = next /. inverseDifferenceDelta -> InverseDifferenceDelta;
  Expand[next] /; FreeQ[next, $Failed]
  ]

GenerateNextSymmetry[___] := Throw[$Failed]

(********************************************************************************************************************)

InverseDifferenceDelta[0, {n_, t_}] := 0

InverseDifferenceDelta[expr_, {n_, t_}] := Block[{funlist, e, res},
  funlist = FindShiftedFunctions[expr, {n, t}];
  (
    e = expr /. (#[n + p_., t] :> #[n + p] & /@ funlist);
    (
      res = DiscreteHomotopyH[e, funlist, n];
      (
        (res /. (#[n + p_.] -> #[n + p, t] & /@ funlist)) /;
         PossibleZeroQ[Expand[Simplify[DifferenceDelta[res, n] - e]]]
        ) /; res =!= $Failed
      ) /;
     ExpressionDoesNotContainTermsWhichAreFunctionsOfIndependentVariableOnlyQ[e, funlist, n]
    ) /; VectorQ[funlist] && Length[funlist] > 0
  ]

InverseDifferenceDelta[___] := $Failed

ExpressionDoesNotContainTermsWhichAreFunctionsOfIndependentVariableOnlyQ[expr_, funlist_, n_] :=
 Block[{m},
  FreeQ[Expand[expr] /. {a_*(b_)[n + p_.]^_. /; ! FreeQ[a, n] &&
        MemberQ[funlist, b] :>
      b[Unique[m, Temporary]], (b_)[n + p_.]^_. /;
       MemberQ[funlist, b] :> b[Unique[m, Temporary]]}, n]]

DiscreteHomotopyH[expr_, funlist_, n_] :=
 Block[{lambda, res, lambdazero}, lambda = Unique[lambda, Temporary];
  res = expr /. (q_ /; MemberQ[funlist, q])[n + r_.] :> lambda*q[n + r];
  lambdazero =
   Which[Quiet[PossibleZeroQ[Limit[res, lambda -> 0]]], 0,
    Quiet[PossibleZeroQ[Limit[res, lambda -> Infinity]]], Infinity,
    True, $Failed];
  (res = discreteHomotopyH[expr, funlist, n, lambdazero];
    res /; res =!= $Failed) /; lambdazero =!= $Failed]

DiscreteHomotopyH[___] := $Failed

FindShiftedFunctions[expr_, {n_, t_}] :=
 Block[{funs},
  funs = Union[Cases[expr, w_[n + i_, t] /; IntegerQ[i] :> w, -1]];
  funs /; VectorQ[funs] && Length[funs] > 0]

FindShiftedFunctions[___] := $Failed

discreteHomotopyH[f_, u_List, n_, lambdazero : 0 | Infinity] :=
 Block[{e, m, lambda}, e = Flatten[FindShifts[f, #, n] & /@ u];
  (m = Min[e];
    If[m < 0, e = DiscreteShift[f, {n, -m}], e = f];
    (e = (discreteHomotopyI[e, #, n] &) /@ u;
      (lambda = Unique[lambda, Temporary];
        e =
         Total[e /. (a_ /; MemberQ[u, a])[n + p_.] :>
             lambda*a[n + p]]/lambda;
        e = Integrate[e, lambda];
        (e =
           Quiet[(e /. lambda -> 1) -
             If[lambdazero == 0, e /. lambda -> 0,
              Limit[e, lambda -> Infinity]]];
          (If[m < 0, DiscreteShift[e, {n, m}], e]) /;
           Quiet[FreeQ[e,
             Limit | DirectedInfinity | Indeterminate | Interval]]) /;
         Quiet[FreeQ[e, Integrate]]) /; FreeQ[e, $Failed]) /;
     DiscreteExactQ[e, u, n]) /; FreeQ[e, $Failed]]

discreteHomotopyH[___] := $Failed

discreteHomotopyI[f_, u_, n_] :=
 Block[{m, i, j}, m = FindShifts[f, u, n];
  (m = Max[m];
    Expand[
     Sum[(-1)^(i - j)*Binomial[i, j]*
       DiscreteShift[
        u[n]*DiscreteVariationalL[f, u, n, i + 1], {n, j}], {i, 0,
       m - 1}, {j, 0, i}]]) /; m =!= $Failed]

discreteHomotopyI[___] := $Failed

DiscreteExactQ[f_, u_List, n_] :=
 And @@ (PossibleZeroQ[DiscreteVariationalL[f, #, n]] & /@ u)

DiscreteExactQ[___] := False

FindShifts[f_, u_, n_] :=
 Block[{test}, test = Cases[{f}, u[n + i_.] :> i, Infinity];
  Union[test] /; (Length[test] > 0 &&
     Apply[And, Map[IntegerQ[#] &, test]])]

FindShifts[___] := $Failed

DiscreteVariationalL[f_, u_, n_, order_: 0] :=
 Block[{shifts, m, k}, shifts = FindShifts[f, u, n];
  (m = Min[shifts];
    (m = Max[shifts];
      m =
       Sum[Binomial[k, order]*DiscreteShift[f, {n, -k}], {k, order,
         m}];
      Expand[D[m, u[n]]]) /; m >= 0) /; shifts =!= $Failed]

DiscreteVariationalL[___] := $Failed

End[];

SetAttributes[{DDERecursionOperator, GenerateSymmetries, InverseDifferenceDelta}, ReadProtected];

Protect[{DDERecursionOperator, GenerateSymmetries, InverseDifferenceDelta}];

EndPackage[];

$ContextPath =
  Flatten[{"Integrability`DDERecursionOperator`",
    "Integrability`InvariantsSymmetries`", oldContextPath}];

Print["Package DDERecursionOperator.m of March 7, 2010 is successfully loaded."];

(* *************************** end of all ********************************* *)
