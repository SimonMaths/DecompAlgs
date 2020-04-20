/*

Functions for finding the Miyamoto group associated to a decomposition algebra

*/
/*

======= Functions for finding a group =======

*/
intrinsic CharacterGroup(G::Grp, R::Rng) -> Grp, Map
  {
    Return the abelian group A isomorphic to the group of homomorphisms G -> R* 
      together with a map translating elements of A to maps.
  }
  A,a := AbelianQuotient(G);
  MG,mg := MultiplicativeGroup(R);
  H,h := Hom(A,MG);
  mp := map<G->R|g:->R!0>;
  return H, map< H -> Parent(mp) | x:-> map<G -> R| g:-> g@a@h(x)@mg > >;
end intrinsic;

intrinsic MiyamotoElement(D::Dec, x::Map) -> GrpElt 
  {
    Returns the Miyamoto element for the decomposition D, associated to the 
      character x.
  }
  F := FusionLaw(D);
  G,m := Grading(F);
  error if not G eq Domain(x), "Character is from the wrong group.";
  BM := Matrix(&cat[ Basis(Part(D,i)) : i in Elements(F) ]);
  M := DiagonalMatrix(&cat[ [ x(m(e)) : i in [1..Dimension(Part(D,e))] ] : e in Elements(F) ]);
  return BM^-1 * M * BM, BaseRing(Parent(D));
end intrinsic;

intrinsic MiyamotoGroup(A::DecAlg, x::Map) -> Grp
  {
    Returns the Miyamoto group of A for the given character x.
  }
  F := FusionLaw(A);
  G := Grading(F);
  GLN := GL(Dimension(A), BaseRing(A));
  M := sub<GLN | [ MiyamotoElement(D, x) : D in Values(Decompositions(A)) ] >;
  return M;
  //FP,FPtoM := FPGroup(M);
  //PM,FPtoPM := PermutationGroup(FP);
  //return PM,hom<PM -> M | [ PM.i@@FPtoPM@FPtoM : i in [1..Ngens(PM)] ] >;
end intrinsic;

intrinsic IsMiyamotoClosed(A::DecAlg, x::Map) -> BoolElt, Assoc
  {
    Returns whether or not A is Miyamoto closed. If so also returns the 
      permutation of decompositions.
  }
  IS := IndexedSet(IndexSet(A));
  X := Elements(FusionLaw(A));
  Ds := [* Decomposition(A,i) : i in IS *];
  DVS := [ [ Part(D,x) : x in X ] : D in Ds ];
  if #{ [ Dimension(P) : P in Ps ] : Ps in DVS } gt 1 then
    return false;
  end if;
  OriginalBases := [Matrix(&cat[ Basis(VS) : VS in DVSi ]):DVSi in DVS];
  perms := AssociativeArray();
  for idx in [1..#IS] do
    i := IS[idx];
    Di := Ds[idx]; 
    M := MiyamotoElement(Di, x);
    DVSM := [ [ P*M : P in Ps ] : Ps in DVS ];
    NewBases := [Matrix(&cat[ Basis(VS) : VS in DVSMi ]):DVSMi in DVSM];
    isit, perm := IsPermutation(OriginalBases, NewBases);
    if not isit then
      return false;
    end if;
    perms[i] := [ IS[j] : j in perm ];
  end for;
  return true, perms;
end intrinsic;
  
//intrinsic UniversalMiyamotoGroup(A::DecAlg, x::Map) -> Grp
//  {
//    Returns the universal Miyamoto group of A for the given character x.
//  }
//  // NOT YET IMPLEMENTED
//  // return Null;
//end intrinsic;


intrinsic MiyamotoGroup(A::DecAlg) -> Grp
  {
    Returns the full Miyamoto group of A.
  }
  F := FusionLaw(A);
  G := Grading(F);
  CG, cg := CharacterGroup(G, BaseRing(A));
  mgs := [ MiyamotoGroup(A, cg(x)) : x in CG ];
  return g where g is sub<Parent(Rep(Rep(mgs)))|mgs>;
end intrinsic;

intrinsic UniversalMiyamotoGroup(A::DecAlg) -> Grp
  {
    Returns the full universal Miyamoto group of A.
  }
  //error if not IsMiyamotoClosed(A), "A is not Miyamoto closed.";
  F := FusionLaw(A);
  G := Grading(F);
  CG, cg := CharacterGroup(G, BaseRing(A));
  IS := IndexedSet(IndexSet(A));
  FPG,FPGtoCG := FPGroup(CG);
  FreeProd := FreeProduct([ FPG : i in IS] );
  incs := [ hom< FPG -> FreeProd | [ FreeProd.(j+n) : j in [1..Ngens(FPG)] ] > 
                   where n is Ngens(FPG)*(i-1) : i in [1..#IS] ];
  rels := [];
  for a in CG do
    for i in [1..#IS] do
      // Should conjugation be on the other side?
      Rai := [ <j,k> : j in {1..#IS}, k in {1..#IS} | 
        forall{ x : x in CG | ab^-1*Mj*ab eq Mk 
          where ab is MiyamotoElement(Decomposition(A, IS[i]), cg(a))
          where Mj is MiyamotoElement(Decomposition(A, IS[j]), cg(x))
          where Mk is MiyamotoElement(Decomposition(A, IS[k]), cg(x)) } ];
      rels cat:= [ aa^-1*jj*aa*kk^-1 where aa is a@@FPGtoCG@incs[i]
                                     where jj is x@@FPGtoCG@incs[jk[1]]
                                     where kk is x@@FPGtoCG@incs[jk[2]]
                   : jk in Rai, x in CG ];
    end for;
  end for;
  UMiy := quo<FreeProd|rels>;
  Miy := MiyamotoGroup(A);
  prj := hom< UMiy -> Miy | [ 
      MiyamotoElement(Decomposition(A,IS[i]), FPGtoCG(FPG.k)@cg) :
        i in [ 1+(j div Ngens(FPG)) ], k in [ 1+(j mod Ngens(FPG)) ],
        j in [0..Ngens(FreeProd)-1] ] >;
  return UMiy, prj;
end intrinsic;

intrinsic MiyamotoGroup(A::DecAlg, Y::SetEnum[AlgChtrElt]) -> Grp
  {
    Returns the Miyamoto group of A for the set of characters Y.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic UniversalMiyamotoGroup(A::DecAlg, Y::SetEnum[AlgChtrElt]) -> Grp
  { 
    Returns the universal Miyamoto group of A for the set of characters Y.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic MiyamotoGroup(A::DecAlg, Y::SeqEnum[AlgChtrElt]) -> Grp
  {
    Returns the Miyamoto group of A for the sequence of characters Y.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic UniversalMiyamotoGroup(A::DecAlg, Y::SeqEnum[AlgChtrElt]) -> Grp
  { 
    Returns the universal Miyamoto group of A for the sequence of characters Y.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic MiyamotoGModule(A::DecAlg) -> ModGrp
  {
    Returns the module for the full Miyamoto group of A.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic UniversalMiyamotoGModule(A::DecAlg) -> ModGrp
  {
    Returns the module for the full universal Miyamoto group of A.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic MiyamotoGModule(A::DecAlg, x::AlgChtrElt) -> ModGrp
  {
    Returns the module for the Miyamoto group of A for the given character x.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic UniversalMiyamotoGModule(A::DecAlg, x::AlgChtrElt) -> ModGrp
  {
    Returns the module for the universal Miyamoto group of A for the given 
    character x.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic MiyamotoGModule(A::DecAlg, Y::SetEnum[AlgChtrElt]) -> ModGrp
  {
    Returns the module for the Miyamoto group of A for the set of characters Y.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic UniversalMiyamotoGModule(A::DecAlg, Y::SetEnum[AlgChtrElt]) -> ModGrp
  { 
    Returns the module for the universal Miyamoto group of A for the set of 
    characters Y.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic MiyamotoGModule(A::DecAlg, Y::SeqEnum[AlgChtrElt]) -> ModGrp
  {
    Returns the module for the Miyamoto group of A for the sequence of 
    characters Y.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic UniversalMiyamotoGModule(A::DecAlg, Y::SeqEnum[AlgChtrElt]) -> ModGrp
  { 
    Returns the module for the universal Miyamoto group of A for the sequence of 
    characters Y.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;
