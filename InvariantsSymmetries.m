
(* ************************************************************************ *)

(* Last updated and adjusted for Mathematica versions 6 and 7 *)
(* by Unal Goktas on May 13, 2009 in Turkey *)

(* Previously updated by Hereman, Sept. 20, 2007 by Hereman at Christchurch *)
(* Earlier update by Hereman, June 7, 2006 *)

(* ::Package:: *)

(* :Title: InvariantsSymmetries.m *)

(* :Context: Integrability`InvariantsSymmetries` *)
(* :Author: Unal Goktas and Willy Hereman *)

(* :Summary:
    This package is used for the computation of invariants and
    symmetries for systems of partial differential and differential
    difference equations.
*)

(* :Copyright: \[Copyright] 2009 by Unal Goktas and Willy Hereman *)
(* :Package Version: 1.3 *)
(* :Mathematica Version: 7.0 and earlier versions *)
(* :History: Software last updated by Unal Goktas on May 13, 2009 in Turkey *)
(*           Previously updated by Willy Hereman on September 20, 2007 *)
(* :Keywords: conservation law, invariant, symmetry, integrability *)

(* :Sources:

    U. Goktas and W. Hereman,
    Symbolic Computation of Conserved Densities for Systems of Nonlinear
    Evolution Equations, 
    Journal of Symbolic Computation, 24 (1997) 591--621.

    U. Goktas, W. Hereman and G. Erdmann,
    Computation of Conserved Densities for Systems of Nonlinear
    Differential-Difference Equations, 
    Physics Letters A, 236 (1997) 30--38.

    U. Goktas and W. Hereman,
    Computation of Conservation Laws for Nonlinear Lattices,
    Physica D, 123 (1998) 425--436.

    U. Goktas and W. Hereman,
    Invariants and Symmetries for Partial Differential Equations
    and Lattices, in: Proc. Fourth International Conference on 
    Mathematical and Numerical Aspects of Wave Propagation,
    Ed. J.A. DeSanto, SIAM, Philadelphia (1998) 403--407.

    U. Goktas and W. Hereman,
    Computation of Higher-order Symmetries for Nonlinear Evolution
    and Lattice Equations, 
    Advances in Computational Mathematics, 11 (1999) 55--80.

    W. Hereman, U. Goktas, M. Colagrosso, and A. Miller,
    Algorithmic integrability tests for nonlinear differential and 
    lattice equations,
    Computer Physics Communications 115 (1998) 428--446.

    M. Hickman and W. Hereman, 
    Computation of densities and fluxes of nonlinear 
    differential-difference equations, 
    Proceedings Royal Society of London A, 459 (2003) 2705--2729.

    P.J. Olver,
    Applications of Lie Groups to Differential Equations,
    Springer-Verlag (1986)
*)

(* :Warnings: None *)
(* :Limitations: see on line documentation *)
(* :Discussion: see on line documentation *)
(* :Requirements: None *)
(* :Examples: see on line documentation *)

Print["Loading Package InvariantsSymmetries.m of May 13, 2009."]

BeginPackage["Integrability`InvariantsSymmetries`"]

PDEInvariants::usage =
"PDEInvariants[eqn, u, {x, t}, R, opts] finds the invariant
with rank R of a partial differential equation for the function u.
PDEInvariants[{eqn1, eqn2, ...}, {u1, u2, ...}, {x, t}, R, opts]
finds the invariant of a system of partial differential equations.
PDEInvariants[{eqn1, eqn2, ...}, {u1, u2, ...}, {x, t}, {Rmax}, opts]
finds the invariants with rank 0 through Rmax.
PDEInvariants[{eqn1, eqn2, ...}, {u1, u2, ...}, {x, t}, {Rmin, Rmax}, opts]
finds the invariants with rank Rmin through Rmax.
x is understood as the space variable and t as the time variable."

DDEInvariants::usage =
"DDEInvariants[eqn, u, {n, t}, R, opts] finds the invariant
with rank R of a differential difference equation for the function u.
DDEInvariants[{eqn1, eqn2, ...}, {u1, u2, ...}, {n, t}, R, opts]
finds the invariant of a system of differential difference equations.
DDEInvariants[{eqn1, eqn2, ...}, {u1, u2, ...}, {n, t}, {Rmax}, opts]
finds the invariants with rank 0 through Rmax.
DDEInvariants[{eqn1, eqn2, ...}, {u1, u2, ...}, {n, t}, {Rmin, Rmax}, opts]
finds the invariants with rank Rmin through Rmax.
n is understood as the discrete space variable and t as the time variable."

PDESymmetries::usage =
"PDESymmetries[eqn, u, {x, t}, R, opts] finds the symmetry
with rank R of a partial differential equation for the function u.
PDESymmetries[{eqn1, eqn2, ...}, {u1, u2, ...}, {x, t}, R, opts]
finds the symmetry of a system of partial differential equations, where
R is the rank of the first equation in the desired symmetry.
PDESymmetries[{eqn1, eqn2, ...}, {u1, u2, ...}, {x, t}, {Rmax}, opts]
finds the symmetries with rank 0 through Rmax.
PDESymmetries[{eqn1, eqn2, ...}, {u1, u2, ...}, {x, t}, {Rmin, Rmax}, opts]
finds the symmetries with rank Rmin through Rmax.
x is understood as the space variable and t as the time variable."

DDESymmetries::usage =
"DDESymmetries[eqn, u, {n, t}, R, opts] finds the symmetry
with rank R of a differential difference equation for the function u.
DDESymmetries[{eqn1, eqn2, ...}, {u1, u2, ...}, {n, t}, R, opts]
finds the symmetry of a system of differential difference equations, where
R is the rank of the first equation in the desired symmetry.
DDESymmetries[{eqn1, eqn2, ...}, {u1, u2, ...}, {n, t}, {Rmax}, opts]
finds the symmetries with rank 0 through Rmax.
DDESymmetries[{eqn1, eqn2, ...}, {u1, u2, ...}, {n, t}, {Rmin, Rmax}, opts]
finds the symmetries with rank Rmin through Rmax.
n is understood as the discrete space variable and t as the time variable."

WeightedParameters::usage =
"WeightedParameters is an option that determines the parameters with
weight. If WeightedParameters -> {p1, p2, ...}, then p1, p2, .... are
considered as constant parameters with weight. The default is
WeightedParameters -> {}."

WeightRules::usage =
"WeightRules is an option that determines the rules for weights of the 
variables. If WeightRules -> {Weight[u] -> val, ...}, then scaling
properties are determined under these rules. There is a built in checking
mechanism to see if the given rules cause inconsistency."

Weight::usage = "Weight[] denotes the weight of its argument."

MaxExplicitDependency::usage =
"MaxExplicitDependency is an option in finding the invariant and generalized
symmetries of PDEs and DDEs. If MaxExplicitDependency -> Max_Integer, then
program allows explicit dependency of independent variables of maximum degree
of Max. The default is MaxExplicitDependency -> 0."

UndeterminedCoefficients::usage =
"UndeterminedCoefficients is an option that determines the name of the
constant coefficients to use. The default is UndeterminedCoefficients -> C."

Weight::badchoice =
"Your choice(s) for the WeightRules option causes inconsistency in
assigning the scaling symmetries. WeightRules -> `1` may work better!"

Weight::nonuniform1 =
"Given system has at least one equation with terms of unequal rank,
so that scaling properties can not be determined."
  
Weight::nonuniform2 =
"Incompatibility has been cured by assuming auxiliary parameters
with weight."

Weight::nonuniform3 =
"Incompatibility could not been cured. Using the options WeightedParameters
or WeightRules may help."

Weight::dilation =
"Dilation symmetry of the equation(s) is `1` ."

Begin["`Private`"]

Options[PDEInvariants] = Options[PDESymmetries] = 
Options[DDEInvariants] = Options[DDESymmetries] =
    {WeightedParameters -> {}, WeightRules -> {},
     MaxExplicitDependency -> 0, UndeterminedCoefficients -> C}

PDEInvariants[eqn_/; !ListQ[eqn],func_/; !ListQ[func],vars_List,
    R_/; (NumberQ[R] && (R >= 0)),opts___?OptionQ]:=
        PDEInvariants[{eqn},{func},vars,{R,R},opts]

PDEInvariants[eqn_/; !ListQ[eqn],func_/; !ListQ[func],vars_List,
    {Rmin_:0,Rmax_?NumberQ},opts___?OptionQ]:=
        PDEInvariants[{eqn},{func},vars,{Rmin,Rmax},opts]

PDEInvariants[eqns_List,funcs_List,vars_List,R_/; (NumberQ[R] && (R >= 0)),
    opts___?OptionQ]:= PDEInvariants[eqns,funcs,vars,{R,R},opts]

PDEInvariants[eqns_List,funcs_List,vars_List,{Rmin_:0,Rmax_?NumberQ},
    opts___?OptionQ]/;
      (Length[eqns] == Length[funcs] && Length[vars] == 2 &&
       (And @@ (MatchQ[#,_== 0]& /@ eqns)) &&
       (And @@ MapThread[
        (Count[#1[[1]],q_/; MatchQ[q,Derivative[0,1][#2][__]]] == 1 &&
         Count[#1[[1]],q_/; !FreeQ[q,Derivative[_,k_/;k>0][_][__]]] == 1)&,
         {eqns,funcs}]) && NumberQ[Rmin] && (0 <= Rmin <= Rmax) &&
       IntegerQ[MaxExplicitDependency /. {opts} /. Options[PDEInvariants]]):=
    Module[
        {sym = Check[findWeights["PDE",eqns,funcs,vars,opts],
                  Null,Weight::badchoice,Weight::nonuniform3],wpars},

        (Message[Weight::dilation,sym[[1]]];
         sym = filterWeights[funcs,vars,sym,opts];
         (wpars = ((# -> 1 &) /@
            (WeightedParameters /. {opts} /. Options[PDEInvariants]));
          {{#},pdeDensity[eqns /. wpars,funcs,vars,sym,#,opts]}& /@
                 trialRanks[{Rmin,Rmax},Join[sym[[1]],{{_,1}}]]) /;
                     sym =!= Null) /; sym =!= Null
        ]

DDEInvariants[eqn_/; !ListQ[eqn],func_/; !ListQ[func],vars_List,
    R_/; (NumberQ[R] && (R >= 0)),opts___?OptionQ]:=
        DDEInvariants[{eqn},{func},vars,{R,R},opts]

DDEInvariants[eqn_/; !ListQ[eqn],func_/; !ListQ[func],vars_List,
    {Rmin_:0,Rmax_?NumberQ},opts___?OptionQ]:=
        DDEInvariants[{eqn},{func},vars,{Rmin,Rmax},opts]

DDEInvariants[eqns_List,funcs_List,vars_List,R_/; (NumberQ[R] && (R >= 0)),
    opts___?OptionQ]:= DDEInvariants[eqns,funcs,vars,{R,R},opts]

DDEInvariants[eqns_List,funcs_List,vars_List,{Rmin_:0,Rmax_?NumberQ},
    opts___?OptionQ]/;
      (Length[eqns] == Length[funcs] && Length[vars] == 2 &&
       (And @@ (MatchQ[#,_== 0]& /@ eqns)) &&
       (And @@ MapThread[
        (Count[#1[[1]],q_/; MatchQ[q,Derivative[0,1][#2][__]]] == 1 &&
         Count[#1[[1]],q_/; !FreeQ[q,Derivative[_,k_/;k>0][_][__]]] == 1)&,
         {eqns,funcs}]) && NumberQ[Rmin] && (0 <= Rmin <= Rmax) &&
       IntegerQ[MaxExplicitDependency /. {opts} /. Options[DDEInvariants]]):=
    Module[
        {sym = Check[findWeights["DDE",eqns,funcs,vars,opts],
                  Null,Weight::badchoice,Weight::nonuniform3],wpars},

        (Message[Weight::dilation,sym[[1]]];
         sym = filterWeights[funcs,vars,sym,opts];
         (wpars = ((# -> 1 &) /@ 
            (WeightedParameters /. {opts} /. Options[DDEInvariants]));
          {{#},ddeDensity[eqns /. wpars,funcs,vars,sym,#,opts]}& /@
                 trialRanks[{Rmin,Rmax},sym[[1]]]) /; sym =!= Null) /;
                     sym =!= Null
        ]

PDESymmetries[eqn_/; !ListQ[eqn],func_/; !ListQ[func],vars_List,
    R_/; (NumberQ[R] && (R >= 0)),opts___?OptionQ]:=
        PDESymmetries[{eqn},{func},vars,{R,R},opts]

PDESymmetries[eqn_/; !ListQ[eqn],func_/; !ListQ[func],vars_List,
    {Rmin_:0,Rmax_?NumberQ},opts___?OptionQ]:=
        PDESymmetries[{eqn},{func},vars,{Rmin,Rmax},opts]

PDESymmetries[eqns_List,funcs_List,vars_List,R_/; (NumberQ[R] && (R >= 0)),
    opts___?OptionQ]:= PDESymmetries[eqns,funcs,vars,{R,R},opts]

PDESymmetries[eqns_List,funcs_List,vars_List,{Rmin_:0,Rmax_?NumberQ},
    opts___?OptionQ]/; 
      (Length[eqns] == Length[funcs] && Length[vars] == 2 &&
       (And @@ (MatchQ[#,_== 0]& /@ eqns)) &&
       (And @@ MapThread[
        (Count[#1[[1]],q_/; MatchQ[q,Derivative[0,1][#2][__]]] == 1 &&
         Count[#1[[1]],q_/; !FreeQ[q,Derivative[_,k_/;k>0][_][__]]] == 1)&,
         {eqns,funcs}]) && NumberQ[Rmin] && (0 <= Rmin <= Rmax) &&
       IntegerQ[MaxExplicitDependency /. {opts} /. Options[PDESymmetries]]):=
    Module[
        {sym = Check[findWeights["PDE",eqns,funcs,vars,opts],
                  Null,Weight::badchoice,Weight::nonuniform3],wpars},

        (Message[Weight::dilation,sym[[1]]];
         sym = filterWeights[funcs,vars,sym,opts];
         (wpars = ((# -> 1 &) /@ 
            (WeightedParameters /. {opts} /. Options[PDESymmetries]));
          {#,pdeSymmetry[eqns /. wpars,funcs,vars,sym,#,opts]}& /@
               trialSymRanks[funcs,vars,sym[[1]],
                   trialRanks[{Rmin,Rmax},Join[sym[[1]],{{_,1}}]]]) /;
                     sym =!= Null) /; sym =!= Null
        ]

DDESymmetries[eqn_/; !ListQ[eqn],func_/; !ListQ[func],vars_List,
    R_/; (NumberQ[R] && (R >= 0)),opts___?OptionQ]:=
        DDESymmetries[{eqn},{func},vars,{R,R},opts]

DDESymmetries[eqn_/; !ListQ[eqn],func_/; !ListQ[func],vars_List,
    {Rmin_:0,Rmax_?NumberQ},opts___?OptionQ]:=
        DDESymmetries[{eqn},{func},vars,{Rmin,Rmax},opts]

DDESymmetries[eqns_List,funcs_List,vars_List,R_/; (NumberQ[R] && (R >= 0)),
    opts___?OptionQ]:= DDESymmetries[eqns,funcs,vars,{R,R},opts]

DDESymmetries[eqns_List,funcs_List,vars_List,{Rmin_:0,Rmax_?NumberQ},
    opts___?OptionQ]/; 
      (Length[eqns] == Length[funcs] && Length[vars] == 2 &&
       (And @@ (MatchQ[#,_== 0]& /@ eqns)) &&
       (And @@ MapThread[
        (Count[#1[[1]],q_/; MatchQ[q,Derivative[0,1][#2][__]]] == 1 &&
         Count[#1[[1]],q_/; !FreeQ[q,Derivative[_,k_/;k>0][_][__]]] == 1)&,
         {eqns,funcs}]) && NumberQ[Rmin] && (0 <= Rmin <= Rmax) &&
       IntegerQ[MaxExplicitDependency /. {opts} /. Options[DDESymmetries]]):=
    Module[
        {sym = Check[findWeights["DDE",eqns,funcs,vars,opts],
                  Null,Weight::badchoice,Weight::nonuniform3],wpars},

        (Message[Weight::dilation,sym[[1]]];
         sym = filterWeights[funcs,vars,sym,opts];
         (wpars = ((# -> 1 &) /@ 
            (WeightedParameters /. {opts} /. Options[DDESymmetries]));
          {#,ddeSymmetry[eqns /. wpars,funcs,vars,sym,#,opts]}& /@
          trialSymRanks[funcs,vars,sym[[1]],
              trialRanks[{Rmin,Rmax},sym[[1]]]]) /; sym =!= Null) /;
                  sym =!= Null
        ]

findWeights[case_String,eqns_,funcs_,vars_,opts___]:=
    Module[{setUniformRank,wplist,wrlist,psym,list1,list2,list3,backup,sol},

        setUniformRank[list_]:= Map[First[list] == # &,Rest[list]];

        wplist = WeightedParameters /. {opts} /. Options[PDEInvariants];
        wrlist = WeightRules /. {opts} /. Options[PDEInvariants];

        Switch[case,
            "PDE",
             With[{svars = Sequence @@ vars},
              psym = Join[Map[# -> E^(Weight[#]) &,wplist],
               Map[#[svars] -> E^(Weight[#]) &,funcs],
               Map[D[#[svars],{vars[[1]],j_Integer},{vars[[2]],k_Integer}] ->
                           E^(Weight[#]+j-k*Weight[vars[[2]]]) &,funcs],
               {vars[[1]] -> 1/E,vars[[2]] -> E^(-Weight[vars[[2]]])}]],
            "DDE",
             With[{var = vars[[2]]},
              psym = Join[Map[# -> E^(Weight[#]) &,wplist],
               Map[#[_,var] -> E^(Weight[#]) &,funcs],
               Map[D[#[_,var],{var,j_Integer}] -> E^(Weight[#]+j) &,funcs],
               {var -> 1/E}]]
            ];
        list1 = Map[weightedMonomialList[#,funcs,vars,wplist]&,
                    (Part[#,1]& /@ eqns)];
        list1 = Join[Cases[#,q_/;!FreeQ[q,Derivative[0,1][_][__]]],#]& /@
                    list1;
        list2 = PowerExpand[Log[list1 /. psym]];
        backup = list3 = Complement[Flatten[setUniformRank /@ list2],{True}];
        list3 = Union[list3 /. wrlist];
        sol = Flatten[Solve[list3]];
        If[sol =!= {}, sol = {sol,{}}];
        If[sol === {} && list3 =!= {True},
            If[wrlist =!= {} && Solve[backup] =!= {},
                Message[Weight::badchoice,Flatten[Solve[backup]]]; Return[]];
            sol = makeUniform[funcs,list3]];
        Switch[case,
            "PDE",Return[{Union[sol[[1]],wrlist /. sol[[1]],
                      {Weight[vars[[1]]] -> -1}],sol[[2]]}],
            "DDE",Return[{Union[sol[[1]],wrlist /. sol[[1]],
                      {Weight[vars[[2]]] -> -1}],sol[[2]]}]
            ]
        ]

(* modified by Unal Goktas, UG:05/13/2009 *)
If[$VersionNumber >= 4.,
   monomialList[expr_, rootmonomials_, opts___]:=
      Module[{s},
         If[$VersionNumber >= 6.,
            s = GroebnerBasis`DistributedTermsList[expr, rootmonomials, opts],
            s = Internal`DistributedTermsList[expr, rootmonomials, opts]
         ];
         (Times @@ MapThread[Power, {s[[2]], #}]&) /@ (#[[1]]& /@ s[[1]])
      ],
   monomialList = MonomialList
]
(* end modification *)

weightedMonomialList[expr_,funcs_,vars_,list_]:=
    Module[{monomials,wmonomials,loclist = Union[funcs,vars,list]},
        If[expr === 0, {0},
            monomials = Union[rootMonomialList[expr,funcs],vars,list];
(* UG:05/13/2009 *)
            wmonomials = monomialList[expr,monomials,
                          CoefficientDomain -> RationalFunctions];
            mDelete[#,loclist]& /@ mDelete[wmonomials,loclist]
          ]
    ]

rootMonomialList[expr_,funcs_]:= Cases[{expr}, q_ /;
        (Not[And @@ (FreeQ[q,#]& /@ funcs)] && Head[q] =!= Power &&
         Head[q] =!= Times && Head[q] =!= Plus),-1] 

mDelete[(list1_List) | (list1_Times),list2_]:=
    DeleteCases[list1,q_ /; And @@ (FreeQ[q,#]& /@ list2)]

mDelete[list1_,list2_]:= list1
    
makeUniform[funcs_,list_]:=
    Module[
        {i,subsub,subsets,sets,length,sol = {},lefts,rights},

        subsub[l_List]:= subsub[l,{{}}];
        subsub[{},prev_List]:= prev;
        subsub[l_List,prev_List]:=
           subsub[Rest[l],Join[prev,(Append[#,First[l]]&) /@ Reverse[prev]]];
        subsets[l_List]:= Sort[Cases[
            subsub[l],q_List/; 1 <= Length[q] < Length[l]]];

        Message[Weight::nonuniform1];
        length = Length[sets = subsets[list]];
        For[i = 1, sol === {} && i <= length,i++,
            sol = Check[Flatten[Solve[Complement[list,sets[[i]]]]],
                      {},Solve::svars];
            If[Count[sol,
                q_/; MemberQ[funcs,q[[1,1]]] && q[[2]] < 0] > 0,sol = {}];
            If[sol =!= {},
                {lefts,rights} = {#[[1]]& /@ sets[[i]],
                                      #[[2]]& /@ sets[[i]]} /. sol;
                If[And @@ Thread[lefts > rights],
                    Message[Weight::nonuniform2];
                    Return[{sol,Union[lefts-rights]}], sol = {}]
              ]
           ];
        Message[Weight::nonuniform3]; Return[{{},{}}]
        ]

filterWeights[funcs_,vars_,psym_,opts___]:=
    Module[{wpars,sym,symfuncs,symwpars,symvars},

        wpars = WeightedParameters /. {opts} /. Options[PDEInvariants];
        sym = Union[psym[[1]] /. (Weight[a_] -> b_) -> {a,b},
                    {1,#}& /@ psym[[2]]] /. ((# -> 1 &) /@ wpars);
        If[Count[sym,
               q_/; MemberQ[funcs,q[[1]]] && q[[2]] < 0] > 0,Return[]];
        symfuncs = Cases[sym,a_/;
           (MemberQ[funcs,a[[1]]] && NumberQ[a[[2]]] && a[[2]] > 0)] /.
                  a_/; MemberQ[funcs,a] -> a[Sequence @@ vars];
        If[symfuncs === {}, Return[]];
        symwpars = Cases[sym,a_/;
           (NumberQ[a[[1]]] && NumberQ[a[[2]]] && a[[2]] > 0)];
        symvars = Cases[sym,a_/; MemberQ[vars,a[[1]]]];
        sym = Reverse[Sort[Union[symfuncs,symwpars],
                  OrderedQ[{#1[[2]],#2[[2]]}]&]];
        {sym,symvars}
        ]

trialRanks[{R_,R_},sym_]:= {R}

trialRanks[{Rmin_,Rmax_},sym_]:=
    Module[{auxfunc},
        auxfunc[x_,y_]:= Union[Flatten[
            Table[i*y[[2]]+#,{i,0,Floor[(Rmax-#)/y[[2]]]}]& /@ x]];
        DeleteCases[Fold[auxfunc,{0},sym],q_/; q < Rmin]
    ]

trialSymRanks[funcs_,vars_,sym_,trials_]:=
    With[{aux = (funcs /. Apply[Rule,DeleteCases[sym,{q_Symbol,r_?NumberQ}] /.
                    q_[Sequence @@ vars] -> q,{1}]) /. 
                    (q_/;MemberQ[funcs,q] -> 0)},
        (((#-aux[[1]] &) /@ aux) + # &) /@ trials
    ]
        

pdeDensity[eqns_,funcs_,vars_,sym_,rank_,opts___]:=
    Module[
        {roots,density,rhsEqn,euler,system},
        roots = rootDensityMonomials["PDE",sym,rank,opts];
        density = findFormDensity[funcs,vars,rank,roots,opts];
        If[density === 0, Return[{{0}}]];
        rhsEqn[i_]:= Flatten[Solve[eqns[[i]],
                         D[funcs[[i]][Sequence @@ vars],vars[[2]]]]][[1,2]];
        euler = Expand[
                    D[density,vars[[2]]] /.
                        (Derivative[k_Integer,1][f_][Sequence @@ vars] :>
                            D[rhsEqn[Flatten[Position[funcs,f]][[1]]],
                              {vars[[1]],k}])
                    ];
        euler = DeleteCases[
(* WH:05/27/2009 Reversed change x_0 was x_ 0  Unal Goktas UG:05/13/2009 *)
                    EulerD[euler,(#[Sequence @@ vars]&) /@ funcs,vars],x_0];
        euler = Expand[Numerator[Together[euler]]];
        If[Length[euler] == 0, Return[{{density}}]];
        system = Union[Flatten[buildEquationList[#,funcs,vars]& /@ euler]];
        analyzeSystem[eqns,vars,{density},system,opts]
        ]

analyzeSystem[eqns_List,vars_,density_List,system_,opts___]:=
    Module[{i,coef,parlist,unknown,inputlist,output = {}},
      coef = UndeterminedCoefficients /. {opts} /. Options[PDEInvariants];
      parlist = Complement[Flatten[Cases[#,q_Symbol,-1]& /@ eqns],vars];
      unknown = Table[coef[i],{i,1,(Plus @@ (myLength /@ density))}];
      If[parlist === {},
        Return[{density /. Flatten[Solve[system,unknown]]}]];
      inputlist = unknown;
      While[inputlist =!= {},
         Module[{j,input,cond,tempsol,parsol},
             input = ToRules[First[inputlist] == 1];
             inputlist = Drop[inputlist,1];
             cond = Eliminate[system /. input,unknown];
             If[cond =!= False,
                If[cond === True,
                   tempsol = Union[Flatten[Solve[system /. input,unknown]],
                                input];
                   inputlist = Intersection[inputlist,
                       Union[Cases[tempsol,w_/;Last[w] == 0] /. (w_-> 0)->w,
                             Complement[inputlist,First[#]& /@ tempsol]]];
                   output = Append[output,{{cond},density /. tempsol}],
                   parsol = DeleteCases[
                               Solve[Reduce[cond,parlist],parlist],w_/;
                               Intersection[w,(# -> 0 &) /@ parlist] =!= {}];
                   Do[
                     tempsol = Union[Flatten[Solve[system /. parsol[[j]] /.
                                   input,unknown]],input];
                     inputlist = Intersection[inputlist,
                       Union[Cases[tempsol,w_/;Last[w] == 0] /. (w_-> 0)->w,
                             Complement[inputlist,First[#]& /@ tempsol]]];
                     output = Append[output,{parsol[[j]],density /. tempsol}],
                     {j,Length[parsol]}
                     ]
                  ]
               ]
             ]
         ];
      If[output =!= {},Return[output],Return[{Table[0,{Length[density]}]}]]
      ]

myLength[expr_]:= If[Head[expr] === Plus,Length[expr],1]

pdeSymmetry[eqns_,funcs_,vars_,sym_,ranks_,opts___]:=
    Module[
        {i,roots,symmetry,rhsEqn,obstr,eps,system = {}},

        roots = rootDensityMonomials["PDE",sym,#,opts]& /@ ranks;
        symmetry = findFormSymmetry[funcs,vars,ranks,roots,opts];
(* WH:05/27/2009 Reversed change x_0 was x_ 0  Unal Goktas UG:05/13/2009 *)
        If[DeleteCases[symmetry,x_0] === {},Return[{symmetry}]];
        rhsEqn[i_]:= Flatten[Solve[eqns[[i]],
                         D[funcs[[i]][Sequence @@ vars],vars[[2]]]]][[1,2]];
        Do[
          obstr = Expand[
                     (D[symmetry[[i]],vars[[2]]] /.
                          (Derivative[k_,1][f_][Sequence @@ vars]:>
                              D[rhsEqn[Flatten[Position[funcs,f]][[1]]],
                                {vars[[1]],k}])) -
                     (D[rhsEqn[i] /.
                        {Derivative[k_,0][f_][Sequence @@ vars]:>
                           D[f[Sequence @@ vars] +
                            eps*symmetry[[Flatten[Position[funcs,f]][[1]]]],
                              {vars[[1]],k}],
                         f_[Sequence @@ vars]:> 
                           f[Sequence @@ vars] + 
                           eps*symmetry[[Flatten[Position[funcs,f]][[1]]]]},
                        eps] /. eps-> 0) 
                       ];
          system = {system,buildEquationList[obstr,funcs,vars]},
          {i,Length[eqns]}
          ];
        analyzeSystem[eqns,vars,symmetry,Union[Flatten[system]],opts]
        ]

rootDensityMonomials[case_String,sym_,rank_,opts___]:=
    Module[
        {i,j,maxexpdep,monolist,auxfunc},

        maxexpdep = MaxExplicitDependency /. {opts} /. Options[PDEInvariants];

        Switch[case,
            "PDE",
             monolist = Flatten[Table[{sym[[2,1,1]]^i*sym[[2,2,1]]^j,
                         i*sym[[2,1,2]]+j*sym[[2,2,2]]},
                         {i,0,maxexpdep},{j,0,maxexpdep-i}],1],
            "DDE",
             monolist = Table[
                            {sym[[2,1,1]]^i,i*sym[[2,1,2]]},{i,0,maxexpdep}]
            ];
        auxfunc[e1_,e2_]:= Flatten[Table[{#[[1]]*e2[[1]]^i,#[[2]]+i*e2[[2]]},
                               {i,0,Floor[(rank-#[[2]])/e2[[2]]]}]& /@ e1,1];
        Fold[auxfunc,monolist,sym[[1]]]
        ]

findFormDensity[funcs_,vars_,rank_,roots_,opts___]:=
    Module[
      {i,extra,temp,formlist = {},coef},

      Do[
         extra = rank-roots[[i]][[2]];
         temp = roots[[i]][[1]];
         If[IntegerQ[extra] && D[temp,vars[[2]]] =!= 0,
            If[extra == 0,
               formlist = {formlist,{temp}},
               Module[
                  {j,templist1,templist2,trivials = {}},
                  templist1 = Sort[weightedMonomialList[
                          D[temp,{vars[[1]],extra-1}],funcs,vars,{}]];
                  Do[
                     templist2 = Sort[weightedMonomialList[
                                 D[templist1[[j]],vars[[1]]],funcs,vars,{}]];
                     trivials = Union[trivials,{Last[templist2]}];
                     formlist = {formlist,Complement[templist2,trivials]},
                     {j,Length[templist1]}
                    ]
                 ]
              ]
           ],
         {i,Length[roots]}
        ];
      coef = UndeterminedCoefficients /. {opts} /. Options[PDEInvariants];
      formlist = Union[Flatten[formlist]];
      Sum[coef[i]*formlist[[i]],{i,Length[formlist]}]
      ]

auxFormDenSym[vars_,r_,root_]:= If[IntegerQ[r-root[[2]]],
                              D[root[[1]],{vars[[2]],r-root[[2]]}],0];

findFormSymmetry[funcs_,vars_,ranks_,roots_,opts___]:=
    Module[{i,j,k,formlist,symlist = {},coef},
      Do[
        formlist = DeleteCases[
(* WH:05/27/2009 Reversed change x_0 was x_ 0  Unal Goktas UG:05/13/2009 *)
            auxFormDenSym[Reverse[vars],ranks[[i]],#]& /@ roots[[i]],x_0];
        formlist = Union[Cases[formlist,x_?NumberQ],
            Flatten[weightedMonomialList[#,funcs,vars,{}]& /@ formlist]];
        symlist = Append[symlist,formlist],
        {i,Length[ranks]}
        ];
      coef = UndeterminedCoefficients /. {opts} /. Options[PDESymmetries];
      (Plus @@ # &) /@
           (Table[coef[j+Sum[Length[symlist[[k]]],{k,0,i-1}]]*symlist[[i,j]],
            {i,Length[symlist]},{j,Length[symlist[[i]]]}])
      ]

separator[expr_,funcs_,vars_] := 
    Module[
      {expr1 = Expand[expr],length,expr2,expr3,coef,list = hH[],expr3j,i,j},
      If[Head[expr1] === Plus,length = Length[expr1],length = 1];
      Do[
        If[length == 1,expr2 = expr1,expr2 = Part[expr1,i]];
        coef = 1;
        expr3 = FactorList[expr2];
        Do[
          expr3j = Part[expr3,j];
          If[And @@ (FreeQ[expr3j,#]& /@ Union[funcs,vars]),
            coef = coef*Part[expr3j,1]^Part[expr3j,2];
            expr2 = expr2/Part[expr3j,1]^Part[expr3j,2];
            ],
          {j,Length[expr3]}];
        list = hH[list,{coef,expr2}],
        {i,length}];
      List @@ Flatten[list,Infinity,hH]
          ];

buildEquationList[expr_,funcs_,vars_] := 
    Module[
      {nexpr = Expand[expr],eqlist = {},list1,list2,same,i,j},
      eqlist = {eqlist,nexpr /. u_[_,_] :> 0};
      nexpr = nexpr-(nexpr /. u_[_,_] :> 0);
      If[nexpr =!= 0,
        list1 = separator[nexpr,funcs,vars];
        list2 = Union[Table[Part[Part[list1,i],2],{i,Length[list1]}]];
        Do[
          same = Select[list1,SameQ[#[[2]],Part[list2,i]]&];
          eqlist = {eqlist,Sum[Part[Part[same,j],1],{j,Length[same]}]},
          {i,Length[list2]}
          ];
        ];
(* WH:05/27/2009 Reversed change x_0 was x_ 0  Unal Goktas UG:05/13/2009 *)
      (# == 0)& /@ DeleteCases[Union[Flatten[eqlist]],x_0]
          ];

(* EulerD: written by Yu He (1992), simplified *)

EulerD[f_, (y_)[x_, r___], w:{x_, r___}] := 
    Module[{Dfuncs, Dtimes, dummyfunc}, 
      Dfuncs = Union[Cases[{f}, Derivative[__][y][__], Infinity]]; 
      Dtimes = (Head[Head[#1]] & ) /@ Dfuncs /. Derivative -> List; 
      Expand[D[f, y[x, r]] + (ReleaseHold[Thread[dummyfunc[(D[f, 
                   #1] & ) /@ Dfuncs, 
               (Hold[Apply[Sequence, #1]] & ) /@ 
                (Thread[{w, #1}] & ) /@ Dtimes]]] /. dummyfunc -> D) . 
          ((-1)^#1 & ) /@ (Apply[Plus, #1] & ) /@ Dtimes] ]
 
EulerD[f_, v:{(y_)[x_, r___], ___}, w:{x_, r___}] := 
    (EulerD[f, #1, w] & ) /@ v /; 
    If[Apply[And, (MatchQ[#1, _[Apply[Sequence, w]]] & ) /@ v], True]

EulerD[f_, (y_)[x_], x_] := EulerD[f, y[x], {x}]
EulerD[f_, v:{(y_)[x_], ___}, x_] := EulerD[f, v, {x}]

shiftMonomial[expr_,funcs_,vars_] /;
    (And @@ (FreeQ[expr,#]& /@ funcs)):= expr

shiftMonomial[expr_Plus,funcs_,vars_]:= shiftMonomial[#,funcs,vars]& /@ expr

shiftMonomial[expr_,funcs_,vars_]:= expr /.
    (vars[[1]] -> 2*vars[[1]]-expr[[Sequence @@ First[Position[expr,
                                 x_[__] /; MemberQ[funcs,x]]]]][[1]])

ddeDensity[eqns_,funcs_,vars_,sym_,rank_,opts___]:=
    Module[
        {roots,density,rhsEqn,obstr,system},
        roots = rootDensityMonomials["DDE",sym,rank,opts];
        density = findDDEFormDensity[eqns,funcs,vars,rank,roots,opts];
        If[density === 0, Return[{{0}}]];
        rhsEqn[i_,m_]:= Flatten[Solve[eqns[[i]],
          D[funcs[[i]][Sequence @@ vars],vars[[2]]]]][[1,2]] /. vars[[1]]->m;
        obstr = D[density,vars[[2]]] /.
                        (Derivative[0,1][f_][m_,vars[[2]]] :>
                          rhsEqn[Flatten[Position[funcs,f]][[1]],m]);
        obstr = Expand[shiftMonomial[Expand[obstr],funcs,vars]];
        If[Length[obstr] == 0,Return[{{density}}]];
        system = Union[buildEquationList[obstr,funcs,vars]];
        analyzeSystem[eqns,vars,{density},system,opts]
        ]

findDDEFormDensity[eqns_,funcs_,vars_,rank_,roots_,opts___]:=
    Module[
      {i,rhsEqn,formlist,coef},

      rhsEqn[i_,m_]:= Flatten[Solve[eqns[[i]],
          D[funcs[[i]][Sequence @@ vars],vars[[2]]]]][[1,2]] /. vars[[1]]->m;

(* WH:05/27/2009 Reversed change x_0 was x_ 0  Unal Goktas UG:05/13/2009 *)
      formlist = DeleteCases[auxFormDenSym[vars,rank,#]& /@ roots,x_0];
      formlist = Union[Flatten[weightedMonomialList[#,funcs,vars,{}]& /@
          (formlist //. (Derivative[0,k_Integer][f_][m_,vars[[2]]] :>
           D[rhsEqn[Flatten[Position[funcs,f]][[1]],m],{vars[[2]],k-1}]))]];
      formlist = Union[shiftMonomial[#,funcs,vars]& /@ formlist];
      coef = UndeterminedCoefficients /. {opts} /. Options[DDEInvariants];
      Sum[coef[i]*formlist[[i]],{i,Length[formlist]}]
      ]

ddeSymmetry[eqns_,funcs_,vars_,sym_,ranks_,opts___]:=
    Module[
        {i,roots,symmetry,rhsEqn1,rhsEqn2,obstr,eps,system = {}},

        roots = rootDensityMonomials["DDE",sym,#,opts]& /@ ranks;
        symmetry = findDDEFormSymmetry[eqns,funcs,vars,ranks,roots,opts];
(* WH:05/27/2009 Reversed change x_0 was x_ 0  Unal Goktas UG:05/13/2009 *)
        If[DeleteCases[symmetry,x_0] === {},Return[{symmetry}]];
        rhsEqn1[i_,m_]:= Flatten[Solve[eqns[[i]],
          D[funcs[[i]][Sequence @@ vars],vars[[2]]]]][[1,2]] /. vars[[1]]->m;
        rhsEqn2[i_,m_]:= symmetry[[i]] /. vars[[1]]->m;
        Do[
          obstr = Expand[
                     (D[rhsEqn2[i,vars[[1]]],vars[[2]]] /.
                          (Derivative[0,1][f_][m_,vars[[2]]]:>
                              rhsEqn1[Flatten[Position[funcs,f]][[1]],m]))-
                     (D[rhsEqn1[i,vars[[1]]] /.
                        (f_[m_,vars[[2]]]:> f[m,vars[[2]]] +
                            eps*rhsEqn2[Flatten[Position[funcs,f]][[1]],m]),
                        eps] /. eps-> 0)
                       ];
          system = {system,buildEquationList[obstr,funcs,vars]},
          {i,Length[eqns]}
          ];
        analyzeSystem[eqns,vars,symmetry,Union[Flatten[system]],opts]
        ]

findDDEFormSymmetry[eqns_,funcs_,vars_,ranks_,roots_,opts___]:=
    Module[
      {i,j,k,rhsEqn,formlist,symlist = {},coef},

      rhsEqn[i_,m_]:= Flatten[Solve[eqns[[i]],
          D[funcs[[i]][Sequence @@ vars],vars[[2]]]]][[1,2]] /. vars[[1]]->m;
      Do[
        formlist = DeleteCases[
(* WH:05/27/2009 Reversed change x_0 was x_ 0  Unal Goktas UG:05/13/2009 *)
            auxFormDenSym[vars,ranks[[i]],#]& /@ roots[[i]],x_0] //.
            (Derivative[0,k_Integer][f_][m_,vars[[2]]] :>
             D[rhsEqn[Flatten[Position[funcs,f]][[1]],m],{vars[[2]],k-1}]);
        formlist = Union[Cases[formlist,x_?NumberQ],
            Flatten[weightedMonomialList[#,funcs,vars,{}]& /@ formlist]];
        symlist = Append[symlist,formlist],
        {i,Length[ranks]}
        ];
      coef = UndeterminedCoefficients /. {opts} /. Options[DDEInvariants];
      (Plus @@ # &) /@
         (Table[coef[j+Sum[Length[symlist[[k]]],{k,0,i-1}]]*symlist[[i,j]],
           {i,Length[symlist]},{j,Length[symlist[[i]]]}])
      ]

End[];

SetAttributes[PDEInvariants,ReadProtected];
SetAttributes[PDESymmetries,ReadProtected];
SetAttributes[DDEInvariants,ReadProtected];
SetAttributes[DDESymmetries,ReadProtected];

Protect[PDEInvariants,DDEInvariants,PDESymmetries,
    DDESymmetries,WeightedParameters,WeightRules,Weight,
    MaxExplicitDependency,UndeterminedCoefficients];

EndPackage[]

Print["Package InvariantsSymmetries.m of May 13, 2009 is successfully loaded."]

(* ************************************************************************* *)

