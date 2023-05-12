/*

Add the additional classes for axial decomposition algebras and axial algebras.

*/
import "HelperFunctions.m":mult_with_mtrx;


intrinsic GetAlgebra(dir::MonStgElt, name::MonStgElt) -> .
  {}
  A := LoadPartialAxialAlgebra(dir cat "/library/Monster_1,4_1,32/RationalField\(\)/basic_algebras/" cat name cat ".json");
  return AxialAlgebra(A);
end intrinsic;
// --------------------------------------------
//
//         Axial Decomposition Algebras
//
// --------------------------------------------
/*

======= The following are axial versions inheriting the structures above =======

*/
declare type AxlDecAlgElt: DecAlgElt;

declare type AxlDecAlg[AxlDecAlgElt]: DecAlg;

declare type AxlDec: Dec;

declare attributes AxlDecAlg:
  Axis_perm_mod,      // A GModule for the action of Miy as a permutation group on the axes acting on the algebra
  Miyamoto_map_perm;  // A map from the axes to a permutation associated with the action on axes

declare attributes AxlDec:
  axis;               // An (Axl)DecAlgElt

/*

======= AxlDecAlg functions and operations =======

*/
intrinsic Print(A::AxlDecAlg)
  {
  Prints an axial decomposition algebra.
  }
  printf "A %o-dimensional axial decomposition algebra with %o decompositions", Dimension(A), #IndexSet(A);
end intrinsic;

intrinsic Axes(A::AxlDecAlg) -> SetIndx[AxlDecAlgElt]
  {
    Returns the set of axes for A.
  }
  return {@ Axis(Decompositions(A)[k]) : k in IndexSet(A) @};
end intrinsic;

intrinsic IsPrimitive(A::AxlDecAlg) -> BoolElt
  {
  Returns whether the axial decomposition algebra is primitive.
  }
  axes := Axes(A);
  
  return &and[IsPrimitive(a) : a in axes];
end intrinsic;

intrinsic AxialDecompositionAlgebra(mult::ModMatFldElt, ax::ModGrpElt, H::Grp) 
    -> DecAlg
  {
    Creates an axial decomposition algebra from a multiplication and list of
    axes.
  }
  R := BaseRing(mult);
  X := Codomain(mult);
  G := Group(X);
  A := New(AxlDecAlg);
  alg :=  Algebra<R, Dimension(X) | [ [ Eltseq(mult_with_mtrx(x,y,mult)) 
                                     : y in Basis(X) ] : x in Basis(X) ] >;
  A`algebra := alg;
  V := VectorSpace(A);
  RX := Restriction(X, H);
  IC := IsotypicDecomposition(RX);
  Vic := [ sub<V| [V!Eltseq(RX!b):b in Basis(ic)]> : ic in IC ];
  decs := [**];

  parts := AssociativeArray();
  adjnt := AdjointMatrix(A`algebra!Eltseq(ax));

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

  return sc where sc is StandardCopy(RemoveDuplicateDecompositions(A));
end intrinsic; 

/*

======= AxlDecAlgElt functions and operations =======

*/
intrinsic IsAxis(a::AxlDecAlgElt) -> BoolElt, Dec
  {
  Returns whether the element is an axis and if so also returns a decomposition for which it is an axis.  Note that if it is an axis for many decompositions, we just return one such decomposition.
  }
  A := Parent(a);
  axes := Axes(A);
  
  if a notin axes then
    return false, _;
  end if;
  
  so := exists(dec){dec : dec in Decompositions(A) | a eq Axis(dec)};
  assert so;
  
  return true, dec;
end intrinsic;


intrinsic Decomposition(a::AxlDecAlgElt) -> Dec
  {
  Returns a decomposition for which a is the axis.  Note that there may be others.
  }
  so, dec := IsAxis(a);
  require so: "The element is not an axis";
  
  return dec;
end intrinsic;

intrinsic Parts(a::AxlDecAlgElt) -> SeqEnum
  {
  For an axis a, return the parts for a decomposition. Note that there may be others.
  }
  so, dec := IsAxis(a);
  require so: "The element is not an axis";
  
  return Parts(dec);
end intrinsic;

intrinsic IsPrimitive(a::AxlDecAlgElt) -> BoolElt
  {
  Returns whether an axial decomposition algebra element is primitive.  That is, whether the part containing the axis is 1-dimensional.
  }
  // This will check for a being an axis.
  dec := Decomposition(a);
  
  so := exists(P){ P : P in Parts(dec) | Vector(a) in P};
  assert so; // The axis is by definition in some part
  
  return Dimension(P) eq 1;
end intrinsic;

intrinsic Projection(a::AxlDecAlgElt, v::AxlDecAlgElt) -> FldElt
  {
  For a primitive axis a, returns the projection of v to onto the axis a.
  }
  // This will check for a being an axis.
  dec := Decomposition(a);
  
  so := exists(P){ P : P in Parts(dec) | Vector(a) in P};
  assert so; // The axis is by definition in some part
  
  require Dimension(P) eq 1: "The axis is not primitive";
  V := VectorSpaceWithBasis([Vector(a)] cat &cat[ Basis(U) : U in Parts(dec) | U ne P]);
  
  return Coordinates(V, Vector(v))[1];
end intrinsic;

/*
 * AxlDec functions and operations
 */
intrinsic Axis(D::AxlDec) -> AxlDecAlgElt
  {
    Returns the axis for D.
  }
  return D`axis;
end intrinsic;

intrinsic Evaluation(D::AxlDec) -> Map
  {
    Returns the evaluation for D.
  }
  return Evaluation(FusionLaw(D));
end intrinsic;

intrinsic AxialDecomposition(A::DecAlg, S::{@ModTupRng@}, axis::. : labels := func<U|FusionLaw(A)!Position(S, U)>) -> Dec
  {
  Given a set of subspaces S of a decomposition algebra A, creates a Decomposition for A with respect to S.  Optional parameter of label gives the labeling of elements of S; the default is by order in S.
  }
  require IsIndependent(&cat[ Basis(U) : U in S]): "The subspaces given are not a direct sum.";
  require &+S eq VectorSpace(Algebra(A)): "The subspaces given do not span A";
  so, ax:= IsCoercible(A, axis);
  require so: "The axis is not coercible into the decomposition algebra";
  
  D := New(AxlDec);
  D`parent := A;
  D`fusion_law := A`fusion_law;
  D`parts := AssociativeArray([* < U@labels, U> : U in S *]);
  D`axis := ax;
  
  return D;
end intrinsic;


// --------------------------------------------
//
//         Axial Algebras
//
// --------------------------------------------
/*

======= The following are axial algebra versions inheriting the structures above =======

*/
declare type AxlAlgElt: AxlDecAlgElt;

declare type AxlAlg[AxlAlgElt]: AxlDecAlg;

declare attributes AxlAlg:
  Frobenius_form;         // The Frobenius form
  
/*

======= AxlAlg functions and operations =======

*/
intrinsic Print(A::AxlAlg)
  {
  Prints an axial algebra.
  }
  printf "A %o-dimensional axial algebra with %o axes", Dimension(A), #IndexSet(A);
end intrinsic;

intrinsic AxialAlgebra(A::ParAxlAlg) -> axlAlg
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
      S := {@ sub<Vnew | [Vnew | ((A!v)*g)`elt : v in Basis(A`axes[i]``attr[{@k@}])]>
                : k in keys[attr], attr in ["even", "odd"] @};
      D := AxialDecomposition(Anew, S, (A`axes[i]`id*g)`elt);
      Append(~decs, D);
    end for;
  end for;
  
  Anew`decompositions := AssociativeArray([* <i, decs[i]> : i in [1..#decs]*]);
  
  return Anew;
end intrinsic;

intrinsic ChangeField(A::AxlAlg, F::Fld) -> DecAlg
  {
  Changes the field of definition of the axial algebra.  Checks that the eigenvalues do not collapse.
  
  Note that we need to be able to coerce any scalars into the new field.  For example, the rationals to a finite field is ok, but not the other way.
  }
  return ChangeRing(A, F);
end intrinsic;

intrinsic ChangeRing(A::axlAlg, F::Rng) -> DecAlg
  {
  Changes the ring of definition of the axial algebra.  Checks that the eigenvalues do not collapse.
  
  Note that we need to be able to coerce any scalars into the new field.  For example, the rationals to a finite field is ok, but not the other way.
  }
  new_FL := ChangeRing(FusionLaw(A), F);
  
  
  // TO DO
end intrinsic;

/*

======= AxlAlgElt functions and operations =======

*/
