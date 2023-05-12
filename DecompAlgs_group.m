/*

Functions for finding the Miyamoto group associated to a decomposition algebra

*/

declare verbose DecompAlgsGrp, 1; 

/*

======= Functions for finding a group =======

*/

intrinsic CharacterGroup(G::Grp, R::Rng) -> Grp, Map
  {
    Return the abelian group Z isomorphic to the group of homomorphisms G -> R* 
      together with a map translating elements of Z to maps.
  }
  A,a := AbelianQuotient(G);
  MG,mg := MultiplicativeGroup(R);
  MG := sub<MG|[ i : i in Generators(MG) | Order(i) ne 0]>;
  H,h := Hom(A,MG);
  mp := map<G->R|g:->R!0>;
  return H, map< H -> Parent(mp) | x:-> map<G -> R| g:-> g@a@h(x)@mg > >;
end intrinsic;

intrinsic CharacterGroup(A::DecAlg) -> Grp, Map
  {
    Return the abelian group Z isomorphic to the group of homomorphisms G -> R* 
      together with a map translating elements of Z to maps, where G is the 
      grading on the fusion law for A and R* is the multiplicative group of its 
      coefficient ring.
  }
  if not assigned A`chargroup then
    F := FusionLaw(A);
    G := Grading(F);
    R := BaseRing(A);
    A`chargroup, A`charmap := CharacterGroup(G, R);
  end if;
  return A`chargroup, A`charmap;
end intrinsic;

function miy_matrix(A,i,x);
  F := FusionLaw(A);
  X := Elements(F);
  _, gr := Grading(F);
  D := Decompositions(A)[i]; 
  BM := Matrix(&cat[ Basis(Part(D,i)) : i in X ]);
  M := DiagonalMatrix(&cat[ [ x(gr(e)) : i in [1..Dimension(Part(D,e))] ] : e in X ]);
  return BM^-1 * M * BM;
end function;

function matgrp_to_permgrp(MG);
  vprintf DecompAlgsGrp: "    Calculating FP group... [";
  FP, FPToMG := FPGroup(MG);
  vprintf DecompAlgsGrp: "done]\n";
  vprintf DecompAlgsGrp: "    Reducing generators... [";
  Red, FPToRed := ReduceGenerators(FP);
  vprintf DecompAlgsGrp: "done]\n";
  vprintf DecompAlgsGrp: "    Calculating permutation group... [";
  PG, RedToPG := PermutationGroup(Red);
  vprintf DecompAlgsGrp: "done]\n";
  vprintf DecompAlgsGrp: "    Building hom... [";
  hm := hom< PG -> MG | [ PG.i@@RedToPG@@FPToRed@FPToMG : i in [1..Ngens(PG)] ] >;
  vprintf DecompAlgsGrp: "done]\n";
  return PG, hm;
end function;

intrinsic MiyamotoGroup(A::DecAlg) -> Grp
  {
    Returns the full Miyamoto group for A.
  }
  if not assigned A`Miyamoto_group then
    sym := Sym(IndexSet(A));
    CG, cg := CharacterGroup(A);
    IS := GSet(sym);
    vprintf DecompAlgsGrp: "    Calculating matrices... [";
    mats := {};
    pdec := 0;
    cnt := 0;
    dd := Max((#IS * #CG) div 10,1);
    for i in IS do
      for x in CG do
        mat := miy_matrix(A,i,cg(x));
        Include(~mats, mat);
        cnt +:= 1;
        if pdec ne cnt div dd then
          vprintf DecompAlgsGrp: "%o", pdec;
          pdec := cnt div dd;
        end if;
      end for;
    end for;
    vprintf DecompAlgsGrp: "]\n";
    vprintf DecompAlgsGrp: "    Calculating matrix group... ";
    n := Dimension(A);
    R := BaseRing(A);
    GLN := GL(n,R);
    M := sub<GLN | mats >;
    vprintf DecompAlgsGrp: "done]\n";
    vprintf DecompAlgsGrp: "    Reducing generators... [";
    smallgens := [];
    smallM := sub<M|>;
    for i in [1..Ngens(M)] do
      if M.i notin smallM then
        Append(~smallgens, M.i);
        smallM := sub<M|smallgens>;
      end if;
    end for;
    vprintf DecompAlgsGrp: "done]\n";
    vprintf DecompAlgsGrp: "    Calculating hom to perm group... [";
    X := Elements(FusionLaw(A));
    Ds := [* Decompositions(A)[i] : i in IS *];
    DVS := [ [ Part(D,x) : x in X ] : D in Ds ];
    OriginalBases := [ [ Basis(VS) : VS in DVSi ]:DVSi in DVS ];
    mattoperm := AssociativeArray();
    for gen in [1..Ngens(smallM)] do
      mat := smallM.gen;
      DVSM := [ [ P*mat : P in Ps ] : Ps in DVS ];
      NewBases := [ [ Basis(VS) : VS in DVSMi ]:DVSMi in DVSM ];
      isit, perm := IsPermutation(OriginalBases, NewBases);
      if not isit then
        vprintf DecompAlgsGrp: "failed]\n";
        A`Miyamoto_group, A`Miyamoto_map :=  matgrp_to_permgrp(smallM);
        return A`Miyamoto_group;
      end if;
      mattoperm[mat] := sym!GSet(sym)[perm];
    end for;
    smallMtoP := hom< smallM -> sym |
                [ mattoperm[smallM.i] : i in [1..Ngens(smallM)] ] >;
    vprintf DecompAlgsGrp: "done]\n";
    if IsTrivial(Kernel(smallMtoP)) then
      vprintf DecompAlgsGrp: "    Calculating isomorphism to perm group of decomps... [";
      im := Image(smallMtoP);
      mp := hom< im -> smallM | [ smallM.i : i in [1..Ngens(smallM)] ] >;
      A`Miyamoto_group := im;
      A`Miyamoto_map := mp;
      vprintf DecompAlgsGrp: "done]\n";
    else
      vprintf DecompAlgsGrp: "    Map to perm group has non-trivial kernel: using standard techniques:\n";
      A`Miyamoto_group, A`Miyamoto_map :=  matgrp_to_permgrp(smallM);
    end if;
  end if;
  return A`Miyamoto_group;
end intrinsic;

intrinsic MiyamotoAction(A::DecAlg, g::GrpElt) -> Mtrx
  {
    Given an element of the Miyamoto group g, return the matrix representing its 
      action on A.
  }
  Miy := MiyamotoGroup(A);
  return A`Miyamoto_map(g);
end intrinsic;

intrinsic MiyamotoElement(A::DecAlg, i::., x::GrpElt) -> GrpElt
  {
    Returns the Miyamoto element \tau_i,x.
  }
  Miy := MiyamotoGroup(A);
  CG, cg := CharacterGroup(A);
  mtrx := miy_matrix(A, i, cg(x));
  return mtrx@@A`Miyamoto_map;
end intrinsic;

intrinsic MiyamotoPermutation(A::DecAlg, i::., x::GrpElt) -> GrpElt
  {
    perm;
  }
  sym := Sym(IndexSet(A));
  CG, cg := CharacterGroup(A);
  IS := GSet(sym);
  X := Elements(FusionLaw(A));
  Ds := [* Decompositions(A)[i] : i in IS *];
  DVS := [ [ Part(D,x) : x in X ] : D in Ds ];
  OriginalBases := [ [ Basis(VS) : VS in DVSi ]:DVSi in DVS ];
  M := MiyamotoAction(A, MiyamotoElement(A, i, x));
  DVSM := [ [ P*M : P in Ps ] : Ps in DVS ];
  NewBases := [ [ Basis(VS) : VS in DVSMi ]:DVSMi in DVSM ];
  isit, perm := IsPermutation(OriginalBases, NewBases);
  require isit: "A is not Miyamoto closed with respect to given element.";
  return sym!IS[perm];
end intrinsic;

intrinsic IsMiyamotoClosed(A::DecAlg, x::GrpElt) -> BoolElt, SetMulti
  {
    Returns whether or not A is Miyamoto closed with respect to the character x.
  }
  if ISA(Type(A), AxlDecAlg) then
    isaxl := true;
  else
    isaxl := false;
  end if;
  CG, cg := CharacterGroup(A);
  IS := IndexedSet(IndexSet(A));
  X := Elements(FusionLaw(A));
  Ds := [* Decompositions(A)[i] : i in IS *];
  if isaxl then
    DVS := [ <Vector(Eltseq(Axis(D))),[ Part(D,x) : x in X ]> : D in Ds ];
    OriginalBases := {* <DVSi[1],[ Basis(VS) : VS in DVSi[2] ]> :DVSi in DVS *};
  else
    DVS := [ [ Part(D,x) : x in X ] : D in Ds ];
    OriginalBases := {* [ Basis(VS) : VS in DVSi ]:DVSi in DVS *};
  end if;
  for idx in [1..#IS] do
    i := IS[idx];
    M := MiyamotoAction(A, MiyamotoElement(A, i, x));
    if isaxl then
      DVSM := [ <Ps[1]*M,[ P*M : P in Ps[2] ]> : Ps in DVS ];
      NewBases := {* <DVSMi[1],[ Basis(VS) : VS in DVSMi[2] ]>:DVSMi in DVSM *};
    else
      DVSM := [ [ P*M : P in Ps ] : Ps in DVS ];
      NewBases := {* [ Basis(VS) : VS in DVSMi ]:DVSMi in DVSM*};
    end if;
    if OriginalBases ne NewBases then 
      return false, NewBases diff OriginalBases;
    end if;
  end for;
  return true, {**};
end intrinsic;

intrinsic IsMiyamotoClosed(A::DecAlg) -> BoolElt, SetMulti
  {
    Returns whether or not A is Miyamoto closed.
  }
  CG, cg := CharacterGroup(A);
  perms := AssociativeArray();
  for x in CG do
    isclosed, extra := IsMiyamotoClosed(A, x);
    if not isclosed then
      return false, extra;
    end if;
  end for;
  return true, {**};
end intrinsic;

intrinsic MiyamotoClosure(A::DecAlg) -> DecAlg, SetMulti
  {
    Returns a Miyamoto closed version of A by adding additional decompositions 
      if needed.
  }
  if ISA(Type(A), AxlDecAlg) then
    isaxl := true;
  else
    isaxl := false;
  end if;
  A :=  StandardCopy(A);
  cnt := #Keys(Decompositions(A));
  isclosed, extra := IsMiyamotoClosed(A);
  vs := VectorSpace(A);
  while not isclosed do
    for x in extra do
      cnt +:= 1;
      if isaxl then
        axis := VectorSpace(A)!x[1];
        parts := {@ sub< vs | xx > : xx in x[2] @};
        (A`decompositions)[cnt] := AxialDecomposition(A, parts, axis);
      else
        parts := {@ sub< vs | xx > : xx in x @};
        (A`decompositions)[cnt] := Decomposition(A, parts);
      end if;
    end for;
    isclosed, extra := IsMiyamotoClosed(A);
  end while;
  return A;
end intrinsic;

intrinsic UniversalMiyamotoGroup(A::DecAlg: Checkclosed:= true) -> Grp, HomGrp
  { 
    Returns the Universal Miyamoto group of A for the subgroup H of the 
      character group. Also returns the projection: UMiy -> Miy.
  }
  if assigned A`universal_Miyamoto_group then
    return A`universal_Miyamoto_group, A`universal_projection;
  end if;
  CG, cg := CharacterGroup(A);
  if Checkclosed then
    vprintf DecompAlgsGrp: "    Checking Miyamoto closed... [";
    require IsMiyamotoClosed(A): "A is not Miyamoto closed.";
    vprintf DecompAlgsGrp: "done]\n";
  end if;
  IS := IndexedSet(IndexSet(A));
  FPG,FPGtoCG := FPGroup(CG);
  FreeProd := FreeProduct([ FPG : i in IS] );
  incs := [ hom< FPG -> FreeProd | [ FreeProd.(j+n) : j in [1..Ngens(FPG)] ] > 
                   where n is Ngens(FPG)*(i-1) : i in [1..#IS] ];
  rels := {};
  MiyEls := AssociativeArray();
  MiyElVals := AssociativeArray();
  vprintf DecompAlgsGrp: "    Generating Miyamoto elements... [";
  for i in [1..#IS] do
    for x in CG do
      mev := MiyamotoElement(A, IS[i], x);
      MiyEls[<i,x>] := mev;
      if mev notin Keys(MiyElVals) then
        MiyElVals[mev] := {};
      end if;
      Include(~(MiyElVals[mev]), <i,x>);
    end for;
  end for;
  vprintf DecompAlgsGrp: "done]\n";
  cnt := 0;
  Tcnt := #Keys(MiyElVals);
  for mev in Keys(MiyElVals) do
    cnt +:= 1;
    vprintf DecompAlgsGrp: "    Calculating relations for (%o/%o)... [", cnt, Tcnt;
    Rai := [ <j,k> : j in {1..#IS}, k in {1..#IS} | 
      forall{ x : x in CG | ab^-1*Mj*ab eq Mk 
        where ab is mev//MiyEls[<i, a>]
        where Mj is MiyEls[<j, x>]
        where Mk is MiyEls[<k, x>] } ];
    rels join:= { aa^-1*jj*aa*kk^-1 where aa is ia[2]@@FPGtoCG@incs[ia[1]]
                                   where jj is x@@FPGtoCG@incs[jk[1]]
                                   where kk is x@@FPGtoCG@incs[jk[2]]
                 : jk in Rai, x in CG, ia in MiyElVals[mev] };
    vprintf DecompAlgsGrp: "done]\n";
  end for;
  vprintf DecompAlgsGrp: "    Calculating quotient group... [";
  Quo := quo<FreeProd|rels>;
  Red, QR := ReduceGenerators(Quo);
  vprintf DecompAlgsGrp: "done]\n";
  vprintf DecompAlgsGrp: "    Calculating projection onto Miyamoto group... [";
  prjimg := [ MiyEls[<i, FPGtoCG(FPG.j)>] :
        i in [ 1+(k div Ngens(FPG)) ], j in [ 1+(k mod Ngens(FPG)) ],
        k in [0..Ngens(FreeProd)-1] ];
  Miy := MiyamotoGroup(A);
  prj := hom< Quo -> Miy | prjimg >;
  vprintf DecompAlgsGrp: "done]\n";
  vprintf DecompAlgsGrp: "    Calculating permutation group... [";
  UMiy, RedToUMiy := PermutationGroup(Red);
  vprintf DecompAlgsGrp: "done]\n";
  A`universal_Miyamoto_group := UMiy;
  vprintf DecompAlgsGrp: "    Converting projection to permutation group... [";
  A`universal_projection := hom< UMiy -> Miy | [ UMiy.i@@RedToUMiy@@QR@prj : 
                i in [1..Ngens(UMiy)] ] >;
  vprintf DecompAlgsGrp: "done]\n";
  return A`universal_Miyamoto_group, A`universal_projection;
end intrinsic;

intrinsic MiyamotoGModule(A::DecAlg) -> ModGrp
  {
    Returns the module for the full Miyamoto group of A.
  }
  Miy := MiyamotoGroup(A);
  return GModule(Miy, [ MiyamotoAction(A, Miy.i) : i in [1..Ngens(Miy)] ]);
end intrinsic;

intrinsic UniversalMiyamotoGModule(A::DecAlg) -> ModGrp
  {
    Returns the module for the full universal Miyamoto group of A.
  }
  UMiy := MiyamotoGroup(A);
  return GModule(UMiy, [ MiyamotoAction(A, A`universal_projection(UMiy.i)) 
        : i in [1..Ngens(UMiy)] ]);
end intrinsic;

intrinsic AxisMiyamotoGSet(A::AxlDecAlg) -> GSet
  {
  Returns the permutation GSet given by the action of the Miyamoto grou on the axes.
  }
  // TO DO
end intrinsic;

