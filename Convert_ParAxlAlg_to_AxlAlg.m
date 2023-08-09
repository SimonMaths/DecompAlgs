// -----------------------------------------------------------
//
// Intrinsics for converting Partial Axial Algebras to Axial Algebras.
//
// -----------------------------------------------------------

intrinsic GetAlgebra(dir::MonStgElt, name::MonStgElt) -> .
  {}
  A := LoadPartialAxialAlgebra(dir cat "/library/Monster_1,4_1,32/RationalField\(\)/basic_algebras/" cat name cat ".json");
  return AxialAlgebra(A);
end intrinsic;

intrinsic AxialAlgebra(A::ParAxlAlg) -> AxlAlg
  {
  Creates an axial algebra from a partial axial algebra.
  }
  Anew := New(AxlAlg);
  Anew`fusion_law := FusionLaw(A`fusion_table);
  Anew`algebra := Algebra<BaseRing(A), Dimension(A) | A`mult>;
  
  eigs := A`fusion_table`eigenvalues;
  Gr, gr := Grading(A`fusion_table);
  require Order(Gr) eq 2: "The grading group must be of order 2";
  
  keys := AssociativeArray();
  keys["even"] := {@ e : e in eigs | e@gr eq Gr!1@};
  keys["odd"] := {@ e : e in eigs | e@gr ne Gr!1@};

  G := Group(A);
  Vnew := VectorSpace(Anew);
  
  // We use a sequence, so there could be duplicate decompositions
  decs := [**];
  for i in [1..#A`axes] do
    H := A`axes[i]`stab;
    trans := Transversal(G, H);
    for g in trans do
      S := [ sub<Vnew | [Vnew | ((A!v)*g)`elt : v in Basis(A`axes[i]``attr[{@k@}])]>
                : k in keys[attr], attr in ["even", "odd"] ];
      D := AxialDecomposition(Anew, S, (A`axes[i]`id*g)`elt);
      Append(~decs, D);
    end for;
  end for;
  
  Anew`decompositions := AssociativeArray([* <i, decs[i]> : i in [1..#decs]*]);
  
  return Anew;
end intrinsic;
