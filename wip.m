intrinsic AxialAlgebra(name::MonStgElt) -> ParAxlAlg
  {
    Get the Norton-Sakuma algebra with the given name.
  }
  name := ToUpper(name);
  error if name notin {"2A","2B","3A","3C","4A","4B","5A","6A"},
    "Valid names are: 2A, 2B, 3A, 3C, 4A, 4B, 5A, 6A";

  return LoadPartialAxialAlgebra("~/magma/AxialAlgebras/library/Monster_1,4_1,32/RationalField\(\)/basic_algebras/" cat name cat ".json");
end intrinsic;

intrinsic JordanAlgebra(n::RngIntElt, q::RngIntElt) -> Alg
  {
    Jordan algbera of n x n matrices over k.
  }
  k := GF(q);
  error if Characteristic(k) eq 2, "Field must be have characteristic different 
    from 2.";
  M := MatrixAlgebra(k,n);
  return Algebra< k, n^2 | [ [ Eltseq((A*B+B*A)/2) : A 
    in Basis(M) ] : B in Basis(M) ] : Rep := "Sparse" >;
end intrinsic;

intrinsic PrimitiveIdempotentsOfJordanAlgebra(J::Alg) -> SetEnum
  {
    Assuming J is a Jordan Algebra return the set of primitive idempotents.
  }
  R := BaseRing(J);
  n := Integers()!Sqrt(Dimension(J));
  VS := VectorSpace(R,n);
  PI := { J!Eltseq(Transpose(Matrix(v))*Matrix(w)) : v in VS, w in VS | 
          InnerProduct(v,w) eq 1 };
  return PI;
end intrinsic;

intrinsic AdjointAction(a::AlgElt) -> Mtrx
  {
    Matrix giving the adjoint action a*-: A -> A.
  }
  A := Parent(a);
  return Matrix([ Eltseq(a*b) : b in Basis(A) ]);
end intrinsic;

intrinsic JordanDecompositionAlgebra(n::RngIntElt, q::RngIntElt) -> DecAlg
  {
    Return the decomposition Jordan decomposition algebra of n x n matrices over 
    k. 
  }
  k := GF(q);
  printf "Creating algebra... [";
  J := JordanAlgebra(n, q);
  printf "done]\n";
  printf "Creating primitives... [";
  PI := PrimitiveIdempotentsOfJordanAlgebra(J);
  printf "done]\n";
  A := New(DecAlg);
  half := (k!2)^-1;
  F := JordanFusionLaw(half);
  A`algebra := J;
  A`fusion_law := F;
  vs := VectorSpace(J);
  decs := AssociativeArray();
  cnt := 0;
  printf "Building decompositions... [";
  pdec := 0;
  dd := #PI div 10;
  for a in PI do
    cnt +:= 1;
    parts := {@ sub<vs | Eigenspace(AdjointAction(a), l) > : l in [k | 1, 0, half ] @};
    decs[cnt] := Decomposition(A, parts);
    if cnt div dd gt pdec then
      printf "%o", pdec;
      pdec := cnt div dd;
    end if;
  end for;
  printf "]\n";
  A`decompositions := decs;
  return A;
end intrinsic;

intrinsic UMiy(A::DecAlg: Checkclosed:= false) -> Grp, HomGrp
  { 
    Returns the Universal Miyamoto group of A for the subgroup H of the 
      character group. Also returns the projection: UMiy -> Miy.
  }
  if assigned A`universal_Miyamoto_group then
    return A`universal_Miyamoto_group, A`universal_projection;
  end if;
  if Checkclosed then
    vprintf DecompAlgsGrp: "     Checking Miyamoto closed... [";
    require IsMiyamotoClosed(A): "A is not Miyamoto closed.";
    vprintf DecompAlgsGrp: "done]\n";
  end if;
  CG, cg := CharacterGroup(A);
  IS := IndexedSet(IndexSet(A));
  vprintf DecompAlgsGrp: "    Getting Miyamoto group:\n";
  Miy := MiyamotoGroup(A);
  vprintf DecompAlgsGrp: "    Building CG^#I x Miy... [";
  PCG,pcg := PermutationGroup(CG);
  BigGrp,inc,prj := DirectProduct([ PCG : i in IS ] cat [ Miy ]);
  vprintf DecompAlgsGrp: "done]\n";
  vprintf DecompAlgsGrp: "    Generating Miyamoto elements... [";
  MiyEls := AssociativeArray();
  MiyElVals := AssociativeArray();
  for x in CG do
    // Maybe the identity is needed? 
    //if IsIdentity(x) then continue; end if; 
    for i in [1..#IS] do
      mev := MiyamotoElement(A, IS[i], x);
      MiyEls[<i,x>] := mev;
      if mev notin Keys(MiyElVals) then
        MiyElVals[mev] := {};
      end if;
      Include(~(MiyElVals[mev]), <i,x>);
    end for;
  end for;
  incSG := map< Keys(MiyEls) -> BigGrp | 
            ix:-> inc[ix[1]](ix[2]@@pcg)*inc[#inc](MiyEls[ix]) >; 
  SubGrp := sub<BigGrp | [ incSG(ix) : ix in Keys(MiyEls) ] >;
  vprintf DecompAlgsGrp: "done]\n";
  vprintf DecompAlgsGrp: "    Computing relations... [";
  rels := {};
  Tcnt := #Keys(MiyElVals) * #IS;
  pdec := 0;
  dd := Max(Tcnt div 10, 1);
  cnt := 0;
  for ab in Keys(MiyElVals) do
    for j in [1..#IS] do
      ks := &meet[ { kx[1] : kx in MiyElVals[ab^-1*Mj*ab] | kx[2] eq x } : 
             Mj in [ MiyEls[<j,x>] ], x in CG ];
      rels join:= { aa^-1*jj*aa*kk^-1 
        where aa is incSG(iy) where jj is incSG(<j,x>) where kk is incSG(<k,x>)
          : k in ks, x in CG, iy in MiyElVals[ab] };
      cnt +:= 1;
      if cnt div dd ne pdec then
        vprintf DecompAlgsGrp: "%o", pdec;
        pdec := cnt div dd;
      end if;
    end for;
  end for;
  vprintf DecompAlgsGrp: "]\n";
  vprintf DecompAlgsGrp: "    Calculating quotient group... [";
  UMiy, proj := quo<SubGrp|rels>;
  vprintf DecompAlgsGrp: "done]\n";
  vprintf DecompAlgsGrp: "    Reducing generators... [";
  RedGrp := sub<UMiy|>;
  gens := [];
  for i in [1..Ngens(UMiy)] do
    if UMiy.i notin RedGrp then
      Append(~gens, UMiy.i);
      RedGrp, incl := sub<UMiy|gens>;
    end if;
  end for;
  vprintf DecompAlgsGrp: "done]\n";
  vprintf DecompAlgsGrp: "    Calculating projection to Miyamoto group... [";
  UMiyToMiy := hom< RedGrp -> Miy | [ (BigGrp!(RedGrp.i@incl@@proj))@prj[#prj] 
                                      : i in [1..Ngens(RedGrp)] ] >;
  vprintf DecompAlgsGrp: "done]\n";
  return RedGrp, UMiyToMiy;
end intrinsic;

intrinsic UKrn(A::DecAlg: Checkclosed:= false) -> Grp, HomGrp
  { 
    Returns the Universal Miyamoto group of A for the subgroup H of the 
      character group. Also returns the projection: UMiy -> Miy.
  }
  if assigned A`universal_Miyamoto_group then
    return Kernel(A`universal_projection);
  end if;
  if Checkclosed then
    vprintf DecompAlgsGrp: "     Checking Miyamoto closed... [";
    require IsMiyamotoClosed(A): "A is not Miyamoto closed.";
    vprintf DecompAlgsGrp: "done]\n";
  end if;
  vprintf DecompAlgsGrp: "    Getting Miyamoto group:";
  Miy := MiyamotoGroup(A);
  CG, cg := CharacterGroup(A);
  IS := IndexedSet(IndexSet(A));
  vprintf DecompAlgsGrp: "    Building CG^#I... [";
  go := [ Order(CG.i) : i in [1..Ngens(CG)] ];
  BigGrp := AbelianGroup(&cat[ go : i in IS ]);
  vprintf DecompAlgsGrp: "done]\n";
  vprintf DecompAlgsGrp: "    Generating Miyamoto elements... [";
  MiyEls := AssociativeArray();
  MiyElVals := AssociativeArray();
  MiyBG := AssociativeArray();
  Tcnt := #CG * #IS;
  pdec := 0;
  dd := Max(Tcnt div 10,1);
  cnt := 0;
  for x in CG do
    for i in [1..#IS] do
      mev := MiyamotoElement(A, IS[i], x);
      MiyEls[<i,x>] := mev;
      MiyBG[<i,x>] := x@(hom<CG->BigGrp|[BigGrp.(j+(i-1)*#go):j in [1..#go]]>);
      if mev notin Keys(MiyElVals) then
        MiyElVals[mev] := {};
      end if;
      Include(~(MiyElVals[mev]), <i,x>);
      if cnt div dd ne pdec then
        vprintf DecompAlgsGrp: "%o", pdec;
        pdec := cnt div dd;
      end if;
    end for;
  end for;
  vprintf DecompAlgsGrp: "]\n";
  vprintf DecompAlgsGrp: "    Computing relations... [";
  rels := {};
  Tcnt := #Keys(MiyElVals) * #IS;
  pdec := 0;
  dd := Max(Tcnt div 10,1);
  cnt := 0;
  for ab in Keys(MiyElVals) do
    for j in [1..#IS] do
      ks := &meet[ { kx[1] : kx in MiyElVals[ab^-1*Mj*ab] | kx[2] eq x } : 
             Mj in [ MiyEls[<j,x>] ], x in CG ];
      rels join:= { jj-kk where aa is MiyBG[iy] where jj is MiyBG[<j,x>] 
        where kk is MiyBG[<k,x>] : k in ks, x in CG, iy in MiyElVals[ab] };
      cnt +:= 1;
      if cnt div dd ne pdec then
        vprintf DecompAlgsGrp: "%o", pdec;
        pdec := cnt div dd;
      end if;
    end for;
  end for;
  vprintf DecompAlgsGrp: "]\n";
  vprintf DecompAlgsGrp: "    Calculating quotient group... [";
  UMiy, proj := quo<BigGrp|rels>;
  vprintf DecompAlgsGrp: "done]\n";
  vprintf DecompAlgsGrp: "    Reducing generators... [";
  RedGrp := sub<UMiy|>;
  gens := [];
  for i in [1..Ngens(UMiy)] do
    if UMiy.i notin RedGrp then
      Append(~gens, UMiy.i);
      RedGrp, incl := sub<UMiy|gens>;
    end if;
  end for;
  vprintf DecompAlgsGrp: "done]\n";
  return RedGrp;
end intrinsic;
