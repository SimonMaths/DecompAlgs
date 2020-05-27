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
    Matrix giving the adjoint action -*a: A -> A.
  }
  A := Parent(a);
  M := Matrix([ Eltseq(b*a) : b in Basis(A) ]);
  return M;
end intrinsic;

intrinsic AdjointAction(a::DecAlgElt) -> Mtrx
  {
  }
  return AdjointAction(a`elt);
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


intrinsic UKrn(A::DecAlg) -> Grp, HomGrp
  { 
    Returns the Universal Miyamoto group of A for the subgroup H of the 
      character group. Also returns the projection: UMiy -> Miy.
  }
  vprintf DecompAlgsGrp: "    Getting character group... [";
  CG, cg := CharacterGroup(A);
  IS := IndexedSet(IndexSet(A));
  vprintf DecompAlgsGrp: "done]\n";
  vprintf DecompAlgsGrp: "    Building CG^#I... [";
  go := [ Order(CG.i) : i in [1..Ngens(CG)] ];
  PCG := PermutationGroup(CG);
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
      mev := miy_matrix(A,IS[i],cg(x));
      MiyEls[<i,x>] := mev;
      MiyBG[<i,x>] := &+[ cf[j]*BigGrp.(j+(i-1)*#cf) : j in [1..#cf] ] 
        where cf is Eltseq(x);
      if mev notin Keys(MiyElVals) then
        MiyElVals[mev] := {};
      end if;
      Include(~(MiyElVals[mev]), <i,x>);
      cnt +:= 1;
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

/* ==== Helper functions ==== */
function mult_with_map(x, y, mp);
  x := Vector(Eltseq(x));
  y := Vector(Eltseq(y));
  dx := Degree(x);
  dy := Degree(y);
  rm := Nrows(mp);
  if rm eq dx*dy then
    return mp(Domain(mp)!TensorProduct(x,y));
  elif rm eq dx*(dx+1)/2 then
    error if  dx ne dy, "x and y are not from the same space.";
    return mp(Domain(mp)!SymmetricProduct(x,y));
  end if;
end function;

intrinsic SymmetricProduct(v::ModTupRngElt, w::ModTupRngElt) -> ModTupRngElt
  {
    The (vector) symmetric product of v and w.
  }
  error if not #Eltseq(v) eq #Eltseq(w), "v and w need to be the same length.";
  sp := [ vw : vw in [&+([ v[i]*w[j] ] cat [ v[j]*w[i] : dummy in [1] | 
          i ne j ])], j in [i..Degree(v)], i in [1..Degree(v)] ];
  return Vector(sp);
end intrinsic;
intrinsic SymmetricProduct(v::ModGrpElt, w::ModGrpElt) -> ModTupRngElt
  {
    The (vector) symmetric product of v and w.
  }
  return SymmetricProduct(Vector(v), Vector(w));
end intrinsic;

function ideal_nz_rel(I, r);
  P := Parent(I.1);
  Q := PolynomialRing(BaseRing(P), Ngens(P)+1);
  inc := hom< P -> Q | [Q.(i+1) : i in [1..Ngens(P)]] >;
  prj := hom< Q -> P | [0] cat [P.i : i in [1..Ngens(P)]] >;
  J := ideal< Q | [ b@inc : b in Basis(I) ], (r@inc)*Q.1 - 1 >;
  J := EliminationIdeal(J, 1);
  I := ideal< P | [ b@prj : b in Basis(J) ] >;
  return I;
end function;

function proj_ideal(I, vars);
  P := Parent(I.1);
  Q := PolynomialRing(BaseRing(P), #vars);
  mapvars := [ Q | ];
  cnt := 0;
  for i in [1..Ngens(P)] do
    if P.i in vars then
      cnt +:= 1;
      Append(~mapvars, Q.cnt);
    else
      Append(~mapvars, 0);
    end if;
  end for;
  AssignNames(~Q, [ Sprint(v) : v in vars ]);
  prj := hom< P -> Q | mapvars >;
  I := EliminationIdeal(I, Seqset(vars));
  J := ideal< Q | [ b@prj : b in Basis(I) ] >;
  return J; 
end function;

function ideal_point_basis(I);
  if Dimension(I) le 0 then
    return Variety(I);
  end if;
  P := Parent(I.1);
  bas_elts := [ ];
  _, vs := Dimension(I);
  for v in vs do
    bi := I + ideal< P | P.v - 1, [ P.w : w in vs | w ne v ] >;
      pts := ideal_point_basis(bi);
      for pt in pts do
        Append(~bas_elts, pt);
      end for;
  end for;
  return bas_elts;
end function;

intrinsic MultiplicationsAndAssociatingForms(X::ModGrp: Commutative := false)
  -> .
  {
    Find multiplications with associating forms for the module X.
  }
  require Type(Commutative) eq BoolElt: "Commutative should be a Boolean..";
  R := BaseRing(X);
  require IsField(R): "Module should be over a field.";
  G := Group(X);
  d := Dimension(X);
  if Commutative then
    TX := SymmetricSquare(X);
  else
    TX := TensorProduct(X,X);
  end if;
  T := TrivialModule(G, R);
  multhoms := GHom(TX, X);
  formhoms := GHom(TX, T);
  multbasis := Basis(multhoms);
  formbasis := Basis(formhoms);
  P := PolynomialRing(AlgebraicClosure(R), #multbasis + #formbasis);
  AssignNames(~P, [ "mult_" cat IntegerToString(i) : i in [1..#multbasis] ] cat
                  [ "form_" cat IntegerToString(i) : i in [1..#formbasis] ]);
  multvars := [ P.i : i in [1..#multbasis] ];
  formvars := [ P.(#multbasis+i) : i in [1..#formbasis] ];

  formhoms := KMatrixSpace(formbasis);
  formhoms := KMatrixSpace(formbasis);
  multbasis := [ Matrix(BaseRing(P), Nrows(b), Ncols(b), Eltseq(b)) : b in multbasis ];
  formbasis := [ Matrix(BaseRing(P), Nrows(b), Ncols(b), Eltseq(b)) : b in formbasis ];

  mult := &+[ multvars[i]*ChangeRing(multbasis[i], P) : i in [1..#multbasis] ];
  form := &+[ formvars[i]*ChangeRing(formbasis[i], P) : i in [1..#formbasis] ];

  multhoms := sub<Parent(Rep(multbasis))|multbasis>;
  formhoms := sub<Parent(Rep(formbasis))|formbasis>;

  rels := [];
  for i,j,k in [1..d] do
    Xi := Vector(P, Eltseq(X.i));
    Xj := Vector(P, Eltseq(X.j));
    Xk := Vector(P, Eltseq(X.k));
    ij := mult_with_map(Xi,Xj,mult);
    jk := mult_with_map(Xj,Xk,mult);
    for r in Eltseq(mult_with_map(ij,Xk,form)-mult_with_map(Xi,jk,form)) do
      Append(~rels, r);
    end for;
  end for;
  I := ideal<P|rels>;
  I := ideal_nz_rel(I, &+[ f^2 : f in formvars ]);
  I := ideal_nz_rel(I, &+[ m^2 : m in multvars ]);

  Inzf := ideal_nz_rel(I, &+[ f^2 : f in formvars ]);
  mults_with_forms := sub< multhoms | >;
  multideal := proj_ideal(Inzf, multvars);
  pts := ideal_point_basis(multideal);
  for pt in pts do
    mults_with_forms +:= sub< multhoms | 
                        &+[ multbasis[i]*pt[i] : i in [1..#multbasis] ] >; 
  end for;

  Inzm := ideal_nz_rel(I, &+[ m^2 : m in multvars ]);
  forms_with_mults := sub< formhoms | >;
  formideal := proj_ideal(Inzm, formvars);
  pts := ideal_point_basis(formideal);
  for pt in pts do
    forms_with_mults +:= sub< formhoms | 
                        &+[ formbasis[i]*pt[i] : i in [1..#formbasis] ] >; 
  end for;

  mtof := function(m);
    cds := Coordinates(multhoms, m);
    formideal := I + ideal< P | [ multvars[i] - cds[i] : i in [1..#cds] ] >;
    formideal := proj_ideal(formideal, formvars);
    pts := ideal_point_basis(formideal);
    thisformspace := sub< formhoms | >;
    for pt in pts do
      thisformspace +:= sub< formhoms | 
                          &+[ formbasis[i]*pt[i] : i in [1..#formbasis] ] >;
    end for;
    return thisformspace;
  end function;

  ftom := function(f);
    cds := Coordinates(formhoms, f);
    multideal := I + ideal< P | [ formvars[i] - cds[i] : i in [1..#cds] ] >;
    multideal := proj_ideal(multideal, multvars);
    pts := ideal_point_basis(multideal);
    thismultspace := sub< multhoms | >;
    for pt in pts do
      thismultspace +:= sub< multhoms | 
                          &+[ multbasis[i]*pt[i] : i in [1..#multbasis] ] >;
    end for;
    return thismultspace;
  end function;

  return mults_with_forms, forms_with_mults, mtof, ftom;

  //J := [ I + ideal< P | formvars[i]-1, [ formvars[j] : j in [1..i-1] ] >
  //        : i in [1..#formvars] ];
  //multideal := ideal< P | multvars, formvars >;
  //for j in J do
  //  _ := GroebnerBasis(j);
  //  if Dimension(j) ge 0 then
  //    ei := EliminationIdeal(j, Seqset(multvars));
  //    gb := GroebnerBasis(ei);
  //    multideal := multideal meet ideal< P | [ b : b in gb ] >;
  //  end if;
  //end for;
  //multideal +:=  ideal< P | formvars>;
  //_ := GroebnerBasis(multideal);
  //_, vs := Dimension(multideal);
  //mults := [];
  //forms := [];
  //for v in vs do
  //  bi := multideal + ideal< P | P.v - 1, [ P.w : w in vs | w ne v ] >;
  //  pts := Variety(bi);
  //  for pt in pts do
  //    thismult := &+[ multbasis[i]*pt[i] : i in [1..#multbasis] ];
  //    Append(~mults, thismult);
  //  end for;
  //end for;
  //multswithforms := sub<multhoms | mults>;
  //return multswithforms;
end intrinsic;

intrinsic DualAsGHom(M::ModGrp) -> .
  {
    Dual module of M intepretted as a space of homomorphisms of M to the trivial 
    module.
  }
  DM := Dual(M);
  G := Group(M);
  R := BaseRing(M);
  T := TrivialModule(G, R);
  basis := [ MapToMatrix(hom<M -> T | Transpose(Matrix(b))>) : b in Basis(DM) ];
  return spc where spc is sub< Parent(Rep(basis)) | basis >;
end intrinsic; 

intrinsic TensorProduct(modules::SeqEnum[ModGrp]) -> ModGrp
  {
    Tensor product of a sequence of modules.
  }
  require #modules gt 0: "No modules provided for tensor product.";
  M := modules[1];
  for i in [2..#modules] do
    M := TensorProduct(M, modules[i]);
  end for;
  return M;
end intrinsic;

intrinsic TensorProduct(elts::SeqEnum[ModGrpElt]) -> ModGrpElt
  {
    Tensor product of a sequence module elements.
  }
  require #elts gt 0: "No modules provided for tensor product.";
  e := elts[1];
  for i in [2..#elts] do
    e := TensorProduct(e, elts[i]);
  end for;
  return e;
end intrinsic;

function S3_T_to_mult(s, isom);
  M := Domain(isom);
  DM:= Codomain(isom);
  return Matrix(BaseRing(M), Nrows(s) div Dimension(M), Dimension(M), Eltseq(s))*isom^-1;
end function;

function sym_pair_idx(d,ij);
  i := ij[1];
  j := ij[2];
  b,c := Explode(Sort([Integers() | i,j]));
  error if c gt d, "Index out of bounds.";
  c -:= b;
  b -:= 1;
  bb := (d*(d+1) - (d-b)*(d-b+1))/2;
  cc := c + 1;
  idx := Integers()!(bb+cc);
  return idx;
end function;

function tns_pair_idx(d,ij);
  i := ij[1];
  j := ij[2];
  return (i-1)*d+j;
end function;

function sym_idx_pair(d,idx);
  i := 0;
  while idx gt d do
    idx -:= d;
    d -:= 1;
    i +:= 1;
    error if d le 0, "idx out of bounds.";
  end while;
  return <i+1,i+idx>;
end function; 

function tns_idx_pair(d,idx);
  i := (idx-1) div d;
  j := (idx-1) mod d;
  return <i+1,j+1>;
end function;

function sym_trip_idx(d,ijk);
  i := ijk[1];
  j := ijk[2];
  k := ijk[3];
  a,b,c := Explode(Sort([Integers() | i,j,k]));
  error if c gt d, "Index out of bounds.";
  c -:= b;
  b -:= a;
  a -:= 1;
  aa := (d*(d+1)*(d+2) - (d-a)*(d-a+1)*(d-a+2))/6;
  bb := ((d-a)*(d-a+1) - (d-a-b)*(d-a-b+1))/2;
  cc := c + 1;
  idx := Integers()!(aa+bb+cc);
  return idx;
end function;

function T3_S3(T3, S3, d);
  R := BaseRing(T3);

  matentries := [];
  r := 0;
  for i in [1..d] do
    for j in [1..d] do
      for k in [1..d] do
        r +:= 1;
        Append(~matentries, <r, sym_trip_idx(d,<i,j,k>), R!1>);
      end for;
    end for;
  end for;
  return MapToMatrix(hom<T3 -> S3 | Matrix(R, Dimension(T3), Dimension(S3), matentries)>);
end function;
 
// Picks one possible splitting, do we need to care about the other 
// possibilities?
//intrinsic Splitting(X,Y) -> ., .
//  {
//    For X a summand of Y return the splitting maps i,p where 
//    0 -> X -i-> Y and Y -p-> X with i*p the identity.
//  }
//  DX := DirectSumDecomposition(X);
//  DY := DirectSumDecomposition(Y);
//  _,IC := IsomorphismClasses(DX cat DY);
//  incs := [];
//  prjs := [];
//  for ic in IC do
//    set1 := [ x : x in ic | x le #DX ];
//    set2 := [ x-#DX : x in ic | x gt #DX ];
//    require #set1 le #set2: "X is not a summand of Y.";
//    for i in [1..#set1] do
//      xi := set1[i];
//      yi := set2[i];
//
//      _, prjXi := quo<X|DX[Remove([1..#DX], xi)]>;
//      _, isom := IsIsomorphic(DX[xi], DY[yi]);
//      isom := hom<DX[xi]->DY[yi]|isom>;
//      _, incYi := sub<Y|DY[yi]>;
//      Append(~incs, MapToMatrix(prjXi*isom*incYi));
//
//      _, prjYi := quo<Y|DY[Remove([1..#DY], yi)]>;
//      _, incXi := sub<X|DX[xi]>;
//      Append(~prjs, MapToMatrix(prjYi*Inverse(isom)*incXi));
//    end for;   
//  end for;
//  return &+incs,&+prjs;
//end intrinsic;

intrinsic IsIsomorphism(m::ModMatFldElt) -> Bool
  {
    return true if m is an isomorphism.
  }
  mat := Matrix(m);
  zeromap := MapToMatrix(hom<Codomain(m) -> Domain(m) | 
      [ 0 : i in [1..Dimension(Codomain(m))] ]>);
  if Ncols(mat) ne Nrows(mat) then
    return false, zeromap;
  end if;
  TF, inv := IsInvertible(mat);
  if not TF then
    return false, zeromap;
  end if;
  inv := MapToMatrix(hom<Codomain(m) -> Domain(m) | inv>);
  if IsGHom(inv) then
    return true, inv;
  end if; 
  return false, zeromap;
end intrinsic;

intrinsic Splitting(f::ModMatFldElt) -> ModMatFldElt
  {
    Given a surjections f: X -> Y return an injection g: Y -> X such that
    such that g*f is the identity on Y if such a map can be found.
  }
  X := Domain(f);
  Y := Codomain(f);
  require Y eq Image(f): "Map must be a surjection.";
  K := Kernel(f);
  C := Complement(X,K);
  C,iC := sub<X|C>;
  iC := MapToMatrix(iC);
  isit, g := IsIsomorphism(iC*f);
  require isit: "Cannot find splitting.";
  return g*iC;
end intrinsic;

intrinsic ExtendToTensorSquare(f::ModMatRngElt, M::ModTupRng) -> ModMatGrpElt
  {
    Extend the map f: S^2(M) -> X to a map from the tensor square of M to X.
  }
  d := Dimension(M);
  S2 := Domain(f);
  require Dimension(S2) eq d*(d+1) div 2: "Map must be from symmetric square.";
  T2 := TensorProduct(M,M);
  p2 := Matrix(BaseRing(M), Dimension(T2), Dimension(S2), 
    [<idx,sym_pair_idx(d,ij),1> 
      : ij in [tns_idx_pair(d,idx)], idx in [1..Dimension(T2)] ]);
  return p2*f;
end intrinsic;

intrinsic MultiplicationsWithAssociatingForms(isom::ModMatGrpElt) 
  -> ModMatFld
  {
    Given an isomorphism M -> Dual(M) find multiplications with associating 
    forms from projections of Sym^3(M) to the trivial module.
  }
  M := Domain(isom);
  D := Codomain(isom);
  require Dual(M) eq D: "Map must be from M to Dual(M).";
  require Dimension(Image(isom)) eq Dimension(D): "Map must be an isomorphism,";
  G := Group(M);
  R := BaseRing(M);
  d := Dimension(M);
 // require Characteristic(R) eq 0 or 
 //   Order(G) mod Characteristic(R) ne 0:"Expected ordinary characteristic.";
  require Characteristic(R) notin {2,3}: "Characteristic must not be 2 or 3.";

  //isomspace := isom_to_dual(M);
  //D := Codomain(Rep(isomspace));

  // Setup inclusions and projections
  T2 := TensorPower(M,2);
  S2 := SymmetricPower(M,2);

  //i2,p2 := Splitting(S2,T2);
  i2 := hom<S2->T2|[T2.tns_pair_idx(d,ij) + T2.tns_pair_idx(d,<ij[2],ij[1]>) 
      : ij in [sym_idx_pair(d,idx)], idx in [1..Dimension(S2)] ]>;
  i2 := MapToMatrix(i2)/2;
  p2 := hom<T2->S2|[S2.sym_pair_idx(d,ij)
      : ij in [tns_idx_pair(d,idx)], idx in [1..Dimension(T2)] ]>;
  p2 := MapToMatrix(p2);

  MS2 := TensorProduct(M,S2);
  S3 := SymmetricPower(M,3);

  //i3,p3 := Splitting(S3, XS2);

  ms2idxfunc := func<i,j,k|(i-1)*Dimension(S2)+sym_pair_idx(d,<j,k>)>;

  s3im := [];
  ms2im := [];
  for i in [1..d] do
    for s2idx in [1..Dimension(S2)] do
      jk := sym_idx_pair(d,s2idx);
      j := jk[1]; k := jk[2];
      idx1 := ms2idxfunc(i,j,k);
      idx2 := ms2idxfunc(j,i,k);
      idx3 := ms2idxfunc(k,i,j);
      s3idx := sym_trip_idx(d,<i,j,k>);
      s3im[s3idx] := (MS2.idx1 + MS2.idx2 + MS2.idx3)/3;
      ms2im[idx1] := S3.s3idx;
      ms2im[idx2] := S3.s3idx;
      ms2im[idx3] := S3.s3idx;
    end for;
  end for;
  i3 := MapToMatrix(hom<S3->MS2|s3im>);
  p3 := MapToMatrix(hom<MS2->S3|ms2im>);
    
  T := TrivialModule(G, R);

  Pspc := GHom(S3, T);
  mults := [];
  forms := [];
  idM := MapToMatrix(hom< M -> M | IdentityMatrix(R, d) >);
  for proj in Basis(Pspc) do
    mult := S2_to_D*isom^-1 where S2_to_D is 
      Transpose(Matrix(R, Dimension(M), Dimension(S2), Eltseq(p3*proj)));
    mult := MapToMatrix(hom<S2 -> M | mult>);
    Append(~mults, mult);
    comult := Splitting(mult);
    id_comult := MapToMatrix(hom< T2 -> MS2 | TensorProduct(idM, comult) >);
    form := i2*id_comult*p3*proj;
    Append(~forms, form);
  end for;
  return multspc,formspc 
    where multspc is sub<Parent(Rep(mults))|mults>
    where formspc is sub<Parent(Rep(forms))|forms>;
end intrinsic;

intrinsic MultiplicationsWithAssociatingForms(M::ModGrp) -> ModMatFld
  { 
    Given a self-dual module M with a 1-dimension space of isomorphisms M -> 
    Dual(M), find multiplications with associating 
    forms from projections of Sym^3(M) to the trivial module.
  }
  D := Dual(M);
  gh := GHom(M,D);
  require Dimension(gh) eq 1: 
    "Must have a canonical (up to scaling) choice of isomorphism to Dual(M).";
  return MultiplicationsWithAssociatingForms(gh.1);
end intrinsic;

intrinsic SplittingField(I::RngMPol) -> Fld
  {
    Splitting field for a variety of dimension 0.
  }
  error if Dimension(I) ne 0, "Ideal is not dimension 0.";
  R := BaseRing(I);
  P1 := Parent(I.1);
  P2 := PolynomialRing(R);
  nv := Ngens(P1);
  for i in Reverse([1..nv]) do
    mp := hom< P1 -> P2 | [ P2.1 : i in [1..nv] ] >;
    pl := Basis(EliminationIdeal(I, {i..nv}))[1]@mp;
    if not IsZero(pl) then
      R := SplittingField(pl);
      P1 := ChangeRing(P1, R);
      P2 := ChangeRing(P2, R);
      I := ChangeRing(I, R);
    end if;
  end for;
  return R;
end intrinsic;

intrinsic AxialMultiplications(X::ModGrp, H::Grp, M::SeqEnum[ModMatGrpElt]:
  idempotent := true, max_eigs:= 0) -> .
  {}
  M := [ MapToMatrix(hom<Domain(x)->Codomain(x)|x>) : x in M ];
  return AxialMultiplications(X, H, M: 
    idempotent:= idempotent, max_eigs := max_eigs);
end intrinsic;


intrinsic AxialMultiplications(X::ModGrp, H::Grp, M::SeqEnum[ModMatFldElt]:
  idempotent := true, max_eigs:= 0) -> .
  {
  }
  if max_eigs le 0 then
    max_eigs := Dimension(X);
  end if;
  n := 0;
  while true do
    n +:= 1;
    //"Trying with",n,"eigenvalues.";
    d := Dimension(X);
    F := Field(X);
    R := Restriction(X, H);
    T := TrivialModule(H, F);
    names := [];
    varnum := 0;
    axial_parts := [ X!R!Image(inc.i).1 : i in [1..Dimension(inc)], 
                    inc in [ GHom(T,R) ] ];
    nv := #axial_parts + #M + (n-1) ;
    P := PolynomialRing(F, nv);
    rels := [];
    axis := &+[ P.i*Vector(P, axial_parts[i]) : i in [1..#axial_parts] ];
    axvars := [1..#axial_parts];
    names cat:= [ "axis_" cat IntegerToString(i) : i in [1..#axial_parts] ];
    varnum +:= #axial_parts;
    mult := &+[ P.(varnum+i)*ChangeRing(M[i],P) : i in [1..#M] ];
    multvars := [(varnum+1)..(varnum+#M)];
    names cat:= [ "mult_" cat IntegerToString(i) : i in [1..#M] ];
    varnum +:= #M;
    rels cat:= [ r : r in Eltseq(mult_with_map(axis,axis,mult)-axis) ];
    adjnt := Matrix([ Eltseq(mult_with_map(axis, Parent(axis)!v, mult)) : 
      v in Basis(X) ]);
    idnty := Parent(adjnt)!1;
    zerty := Parent(adjnt)!0;
    zeromatrix := &*([ adjnt - (idempotent select idnty else zerty) ] cat 
                     [ adjnt - P.(varnum+i)*idnty : i in [1..n-1] ]);
    names cat:= [ "ev_" cat IntegerToString(i) : i in [1..n-1] ];
    varnum +:= n-1;
    rels cat:= Eltseq(zeromatrix);
    AssignNames(~P, names);
    I := ideal<P|rels>;
    J := [ I + ideal<P|P.i-1, [P.j:j in [multvars[1]..i-1]]>
            : i in multvars ];
    J := &cat[ PrimaryDecomposition(j) : j in J ];
    foundax := false;
    mt_axs := [];
    XX := X;
    for I in J do 
      if Dimension(I) eq 0 then
        foundax := false;
        mt_ax := AssociativeArray();
        _ := GroebnerBasis(I);
        Q := SplittingField(I);
        splitI := ChangeRing(I, Q);
        X := ChangeRing(XX, Q);
        for pt in Variety(splitI) do
          ax := X!(&+[ pt[i]*Vector(Q, axial_parts[i]) : i in [1..#axial_parts] ]);
          if not IsZero(ax) then
            mt := &+[ pt[i+#axial_parts]*Matrix(Q,M[i]) : i in [1..#M] ];
            mt := MapToMatrix(hom<ChangeRing(Domain(Rep(M)),Q)->X|mt>);
            if not mt in Keys(mt_ax) then
              mt_ax[mt] := [];
            end if;
            if not ax in mt_ax[mt] then
              foundax := true;
              Append(~(mt_ax[mt]), ax);
            end if;
          end if;
        end for;
      end if;
      if foundax then
        Append(~mt_axs, mt_ax);
      end if;
    end for;

    if #mt_axs gt 0 then 
      decalgs := [**];
      for ma in mt_axs do
        for m in Keys(ma) do
          for a in ma[m] do
            A := AxialDecompositionAlgebra(m,a,H);
            Append(~decalgs, A);
          end for;
        end for;
      end for;
      return decalgs;
    else
      require n lt max_eigs: "Cannot find axial multiplication.";
    end if;
  end while;

end intrinsic;

intrinsic IsotypicDecomposition(X::ModGrp) -> SeqEnum
  {
    Return the isotypic decomposition of X.
  }
  T := TrivialModule(Group(X), BaseRing(X));
  D := DirectSumDecomposition(X);
  _,ic := IsomorphismClasses([T] cat D);
  return [ sub<X|D[c]> : c in [[i-1:i in x|i gt 1]], x in ic | #c gt 0 ];
end intrinsic;

intrinsic AxialDecompositionAlgebra(mult::ModMatFldElt, ax::ModGrpElt, H::Grp) -> .
  {
    Creates an axial decomposition algebra from a multiplication and list of
    axes.
  }
  R := BaseRing(mult);
  X := Codomain(mult);
  G := Group(X);
  A := New(AxlDecAlg);
  alg :=  Algebra<R, Dimension(X) | [ [ Eltseq(mult_with_map(x,y,mult)) 
                                     : y in Basis(X) ] : x in Basis(X) ] >;
  A`algebra := alg;
  V := VectorSpace(A);
  RX := Restriction(X, H);
  IC := IsotypicDecomposition(RX);
  Vic := [ sub<V| [V!Eltseq(RX!b):b in Basis(ic)]> : ic in IC ];
  decs := [**];

  parts := AssociativeArray();
  adjnt := AdjointAction(A`algebra!Eltseq(ax));

  for evd in Eigenvalues(adjnt) do
    ev := evd[1];
    d := evd[2];
    Ve := sub<V|Eigenspace(adjnt, ev)>;
    bas := [];
    for i in [1..#Vic] do
      vic := Vic[i];
      vevic := Ve meet vic;
      if Dimension(vevic) gt 0 then
        parts[<i,ev>] := Basis(vevic);
        bas cat:= Basis(vevic);
        d -:= Dimension(vevic);
      end if;
    end for;
    if d gt 0 then
      EB := ExtendBasis(bas, Ve);
      parts[<0,ev>] := sub<Ve|EB[[#bas+1..#EB]]>;
    end if;
  end for;

  keys := [ k : k in Keys(parts) ];
  p1 := [ i : i in [1..#keys] | keys[i][2] eq 1 ];
  p0 := [ i : i in [1..#keys] | keys[i][2] eq 0 ];
  po := [ i : i in [1..#keys] | i notin p1 and i notin p0 ];
  ps1 := [ k[1] : k in keys[p1] ];
  ps0 := [ k[1] : k in keys[p0] ];
  pso := [ k[1] : k in keys[po] ];
  ParallelSort(~ps1, ~p1);
  ParallelSort(~ps0, ~p0);
  ParallelSort(~pso, ~po);
  keys := keys[p1] cat keys[p0] cat keys[po];
  basispart := [];
  for i in [1..#keys] do
    basispart cat:= [ i : b in parts[keys[i]] ];
  end for; 

  VSWB := VectorSpaceWithBasis(&cat[ parts[k] : k in keys ]);
  FLA := AssociativeArray();
  FLA["class"] := "Fusion law";
  FLA["set"] := [1..#keys];
  FLA["law"] := [ [ &join[ { basispart[i] : i in 
      Support(Vector(Coordinates(VSWB,V!(alg!br*alg!bc)))) }
      : bc in parts[c], br in parts[r] ] : c in keys ] : r in keys ];
  FLA["evaluation"] := [ k[2] : k in keys ];
  FL := FusionLaw(FLA);
  A`fusion_law := FL;
  
  for t in Transversal(G,H) do
    S := {@ sub<V | [ V!((X!b)*t) : b in parts[k] ] > : k in keys @};
    D := AxialDecomposition(A, S, V!(ax*t)); 
    Append(~decs, D);
  end for;

  A`decompositions := AssociativeArray([* <i, decs[i]> : i in [1..#decs] *]);

  return StandardCopy(RemoveDuplicateDecompositions(A));
end intrinsic; 

intrinsic Multiplication(A::Alg) -> .
  {
    Multiplication represented as a linear map from the tensor product of A to
    A.
  }
  V := VectorSpace(A);
  d := Dimension(V);
  T := TensorProduct(V,V);
  M := Matrix(BaseRing(A), d*d, d, 
    [ Eltseq(A.ij[1]*A.ij[2]) : ij in [tns_idx_pair(d,idx)], idx in [1..d*d] ]);
  return M;
end intrinsic; 

/*

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

*/
intrinsic IsIsomorphic(A::Alg, B::Alg) -> BoolElt, Mtrx
  {
    Return if the algebras are isomorphic and if so a basis change matrix.
  }
  return IsIsomorphicMultiplication(Multiplication(A), Multiplication(B));
end intrinsic;

intrinsic IsIsomorphicMultiplication(A::Mtrx,B::Mtrx) -> BoolElt, Mtrx
  {
    Given a pair of matrices representing the multiplication map from the tensor 
    product of an algebra to the algebra, return if the algebras are isomorphic 
      and if so a basis change matrix.
  }
  r := Nrows(A);
  c := Ncols(A);
  R := Parent([ Rep(BaseRing(A)), Rep(BaseRing(B)) ][1]);
  A := ChangeRing(A, R);
  B := ChangeRing(B, R);
  require r eq c*c: "Matrices must represent a multiplication.";
  if Nrows(B) ne r or Ncols(B) ne c then
    return false, 0;
  end if;
  if A eq B then
    return true, IdentityMatrix(R, c);
  end if;
  v := c*c+1;
  P := PolynomialRing(R, v);
  A := ChangeRing(A, P);
  B := ChangeRing(B, P);
  BC := Matrix(P, c, c, [ P.i : i in [1..c*c] ]);
  BCinv := Matrix(P, c, c, Cofactors(BC));
  TP := TensorProduct(BC, BC);
  rels := Eltseq(TP*A*BCinv - B*P.v);
  I := ideal<P | rels, Determinant(BC)-1>;
  EI := EliminationIdeal(I, {P.v});
  if Dimension(EI) eq -1 then
    return false, 0;
  end if;
  // I don't think this should ever happen
  if #GroebnerBasis(EI) ne 1 then
    return false, 0;
  end if;
  eqn := Basis(EI)[1];
  PP<x> := PolynomialRing(R);
  mp := hom<P -> PP | [ i eq v select x else 0 : i in [1..v] ] >;
  eqn2 := mp(eqn);
  if Support(eqn2) ne [ 0, c*2 ] then
    return false, 0;
  end if;
  cnst := -Coefficient(eqn2, 0);
  isit, sqrt := IsSquare(cnst);
  if not isit then
    // Though maybe over a bigger field
    return false, 0;
  end if;
  I := ideal<P | rels, Determinant(BC)-(1/sqrt), P.v-(1/sqrt)>;
  VS := VarietySequence(I);
  if #VS eq 0 then
    return false, 0;
  end if;
  scr := [];
  for v in VS do
    Append(~scr, &+[ x eq 1 select 1 else x eq -1 select 11/10 else 3 : x in v]);
  end for;
  ParallelSort(~scr, ~VS);
  return true, Matrix(R, c, c, VS[#VS][1..c*c]);
end intrinsic;


intrinsic ChangeBasis(A::DecAlg, B::Mtrx) -> DecAlg
  {
    Return a copy of A under the basis change given by B. 
  }
  if ISA(Type(A), AxlDecAlg) then
    axl := true;
    Anew := New(AxlDecAlg);
  else
    axl := false;
    Anew := New(DecAlg);
  end if;
  fus := FusionLaw(A); Anew`fusion_law := fus;
  alg := ChangeBasis(Algebra(A), B); Anew`algebra := alg;
  vs := VectorSpace(Anew);
  IS := IndexSet(A);
  oldbases := [ [ Basis(Part(Decompositions(A)[i], x)) : 
               x in Elements(fus) ] : i in IS ];
  bases := [ [ Basis(sub<vs|[b*B^-1:b in bas]>) : bas in y ] : y in oldbases ];
  if axl then
    axes := [ Vector(Eltseq(Axis(Decompositions(A)[i])))*B^-1 : i in IS ];
    ParallelSort(~bases, ~axes);
    Reverse(~bases);
    Reverse(~axes);
  else
    Sort(~bases);
    Reverse(~bases);
  end if;
  decs := AssociativeArray();
  for i in [1..#bases] do
    basis := bases[i];
    parts := {@ sub<vs| b> : b in basis @};
    if axl then
      axis := axes[i];
      Dnew := AxialDecomposition(Anew, parts, axis);
    else
      Dnew := Decomposition(Anew, parts);
    end if;
    decs[i] := Dnew;
  end for;
  Anew`decompositions := decs;
  return Anew;
end intrinsic;

intrinsic RemoveDuplicateDecompositions(A::DecAlg) -> DecAlg
  {
    Return a copy of A with duplicate decompositions removed. A decomposition is 
    a duplicate if the parts are the same. If the decomposition is axial then 
      the axis must also match. Note that a non-axial decomposition with parts 
      identitcal to an axial decomposition will be removed.
  }
  IS := IndexSet(A);
  decs := Decompositions(A);
  fuselts := [ x : x in Elements(FusionLaw(A)) ];
  lookup := AssociativeArray(); 
  for idx in IS do
    dec := decs[idx];
    if IsAxial(dec) then
      axis := Axis(dec);
      isaxl := true;
    else
      axis := A!0;
      isaxl := false;
    end if;
    parts := [ Basis(Part(dec, x)) : x in fuselts ];
    val := <isaxl,axis,idx>;
    if not parts in Keys(lookup) then
      lookup[parts] := { val };
    elif isaxl then
      current := lookup[parts];
      new := [ x : x in current | x[1] ];
      axes := { x[2] : x in new };
      if not axis in axes then
        Append(~new, val);
      end if;
      lookup[parts] := new;
    end if;
  end for;
  keep := { val[3] : val in lookup[key], key in Keys(lookup) };
  remove := { x : x in IS } diff keep;
  return RemoveDecompositions(A, remove);
end intrinsic;
