intrinsic AxialAlgebra(name::MonStgElt) -> ParAxlAlg
  {
    Get the Norton-Sakuma algebra with the given name.
  }
  name := ToUpper(name);
  error if name notin {"2A","2B","3A","3C","4A","4B","5A","6A"},
    "Valid names are: 2A, 2B, 3A, 3C, 4A, 4B, 5A, 6A";

  return LoadPartialAxialAlgebra("~/magma/AxialAlgebras/library/Monster_1,4_1,32/RationalField\(\)/basic_algebras/" cat name cat ".json");
end intrinsic;

intrinsic JordanAlgebra(n::RngIntElt, k::Fld) -> Alg
  {
    Jordan algbera of n x n matrices over k.
  }
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
  ZO := ZeroMatrix(R, n, n);
  ZO[1,1] := 1;
  PI := { J!Eltseq(B*ZO*B^-1) : B in GL(n,R) };
  return PI;
end intrinsic;

intrinsic AdjointAction(a::AlgElt) -> Mtrx
  {
    Matrix giving the adjoint action a*-: A -> A.
  }
  A := Parent(a);
  return Matrix([ Eltseq(a*b) : b in Basis(A) ]);
end intrinsic;

intrinsic JordanDecompositionAlgebra(n::RngIntElt, k::Fld) -> DecAlg
  {
    Return the decomposition Jordan decomposition algebra of n x n matrices over 
    k. 
  }
  J := JordanAlgebra(n, k);
  PI := PrimitiveIdempotentsOfJordanAlgebra(J);
  A := New(DecAlg);
  half := (k!2)^-1;
  F := JordanFusionLaw(half);
  A`algebra := J;
  A`fusion_law := F;
  vs := VectorSpace(J);
  decs := AssociativeArray();
  cnt := 0;
  for a in PI do
    cnt +:= 1;
    parts := {@ sub<vs | Eigenspace(AdjointAction(a), l) > : l in [k | 1, 0, half ] @};
    decs[cnt] := Decomposition(A, parts);
  end for;
  A`decompositions := decs;
  return A;
end intrinsic;
