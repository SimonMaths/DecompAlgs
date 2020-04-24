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
