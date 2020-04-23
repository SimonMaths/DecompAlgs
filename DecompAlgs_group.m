/*

Functions for finding the Miyamoto group associated to a decomposition algebra

*/
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
  FP, fp := FPGroup(MG);
  PG, pg := PermutationGroup(FP);
  return PG, hom< PG -> MG | [ PG.i@@pg@fp : i in [1..Ngens(PG)] ] >;
end function;

intrinsic MiyamotoGroup(A::DecAlg) -> Grp
  {
    Returns the full Miyamoto group for A.
  }
  if not assigned A`Miyamoto_group then
    CG, cg := CharacterGroup(A);
    GLN := GL(Dimension(A), BaseRing(A));
    M := sub<GLN | [ miy_matrix(A,i,cg(x)) : i in IndexSet(A), x in CG  ] >;
    A`Miyamoto_group, A`Miyamoto_map :=  matgrp_to_permgrp(M);
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

intrinsic IsMiyamotoClosed(A::DecAlg, x::GrpElt) -> BoolElt
  {
    Returns whether or not A is Miyamoto closed with respect to the character x.
  }
  CG, cg := CharacterGroup(A);
  IS := IndexedSet(IndexSet(A));
  X := Elements(FusionLaw(A));
  Ds := [* Decompositions(A)[i] : i in IS *];
  DVS := [ [ Part(D,x) : x in X ] : D in Ds ];
  OriginalBases := {* [ Basis(VS) : VS in DVSi ]:DVSi in DVS *};
  for idx in [1..#IS] do
    i := IS[idx];
    M := MiyamotoAction(A, MiyamotoElement(A, i, x));
    DVSM := [ [ P*M : P in Ps ] : Ps in DVS ];
    NewBases := {* [ Basis(VS) : VS in DVSMi ]:DVSMi in DVSM*};
    if OriginalBases ne NewBases then 
      return false, NewBases diff OriginalBases;
    end if;
  end for;
  return true, {**};
end intrinsic;

intrinsic IsMiyamotoClosed(A::DecAlg) -> BoolElt
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

intrinsic MiyamotoClosure(A::DecAlg) -> DecAlg
  {
    Returns a Miyamoto closed version of A by adding additional decompositions 
      if needed.
  }
  A :=  StandardCopy(A);
  cnt := #Keys(Decompositions(A));
  isclosed, extra := IsMiyamotoClosed(A);
  vs := VectorSpace(A);
  while not isclosed do
    for x in extra do
      cnt +:= 1;
      parts := {@ sub< vs | xx > : xx in x @};
      (A`decompositions)[cnt] := Decomposition(A, parts);
    end for;
    isclosed, extra := IsMiyamotoClosed(A);
  end while;
  return A;
end intrinsic;


intrinsic UniversalMiyamotoGroup(A::DecAlg) -> Grp, HomGrp
  { 
    Returns the Universal Miyamoto group of A for the subgroup H of the 
      character group. Also returns the projection: UMiy -> Miy.
  }
  if assigned A`universal_Miyamoto_group then
    return A`universal_Miyamoto_group, A`universal_projection;
  end if;
  CG, cg := CharacterGroup(A);
  error if not IsMiyamotoClosed(A), "A is not Miyamoto closed.";
  IS := IndexedSet(IndexSet(A));
  FPG,FPGtoCG := FPGroup(CG);
  FreeProd := FreeProduct([ FPG : i in IS] );
  incs := [ hom< FPG -> FreeProd | [ FreeProd.(j+n) : j in [1..Ngens(FPG)] ] > 
                   where n is Ngens(FPG)*(i-1) : i in [1..#IS] ];
  rels := {};
  for a in CG do
    for i in [1..#IS] do
      Rai := [ <j,k> : j in {1..#IS}, k in {1..#IS} | 
        forall{ x : x in CG | ab^-1*Mj*ab eq Mk 
          where ab is MiyamotoElement(A, IS[i], a)
          where Mj is MiyamotoElement(A, IS[j], x)
          where Mk is MiyamotoElement(A, IS[k], x) } ];
      rels join:= { aa^-1*jj*aa*kk^-1 where aa is a@@FPGtoCG@incs[i]
                                     where jj is x@@FPGtoCG@incs[jk[1]]
                                     where kk is x@@FPGtoCG@incs[jk[2]]
                   : jk in Rai, x in CG };
    end for;
  end for;
  Quo := quo<FreeProd|rels>;
  Miy := MiyamotoGroup(A);
  prj := hom< Quo -> Miy | [ 
      MiyamotoElement(A,IS[i], FPGtoCG(FPG.j)) :
        i in [ 1+(k div Ngens(FPG)) ], j in [ 1+(k mod Ngens(FPG)) ],
        k in [0..Ngens(FreeProd)-1] ] >;
  UMiy, QuoToUMiy := PermutationGroup(Quo);
  A`universal_Miyamoto_group := UMiy;
  A`universal_projection := hom< UMiy -> Miy | [ UMiy.i@@QuoToUMiy@prj : 
                i in [1..Ngens(UMiy)] ] >;
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

