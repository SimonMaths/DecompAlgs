/*
 *  Package for decomposition algebras and related structures
 *  Authors: Justin McInroy, Simon F. Peacock
 */

/*
 * These are the base types for decomposition algebras
 */

// Need to think more carefully about these attributes!!

declare type DecAlg[DecAlgElt];

declare attributes DecAlg:
  fusion_law,                // A FusLaw
  decompositions,            // An Assoc of Decs
  algebra,                   // The algebra
  Miyamoto_group,            // The Miyamoto group
  Miyamoto_map,              // Miy -> Matrices
  universal_Miyamoto_group,  // Universal Miyamoto group
  universal_projection,      // surjection; UMiy -> Miy
  chargroup,                 // The character group of A
  charmap;                   // the map chargroup -> [hom: grading -> R*]

declare attributes DecAlgElt:
  parent,                    // A FusLaw
  elt;                       // An element of the algebra

declare type Dec;

declare attributes Dec:
  parent,                    // Either an algebra, or a DecAlg
  fusion_law,                // A Fuslaw
  parts;                     // An Assoc indexed by the elements of the fusion law

forward CreateElement; // This is defined half-way down the file, but we want to use it first.
/*

======= Additional utility functions =======
*/
function mult_with_map(x, y, mp);
  x := Vector(Eltseq(x));
  y := Vector(Eltseq(y));
  dx := Degree(x);
  dy := Degree(y);
  rm := Nrows(mp);
  if rm eq dx*dy then
    return mp(Domain(mp)!TensorProduct(x,y));
  elif rm eq dx*(dx+1)/2 then
    error if dx ne dy, "x and y are not from the same space.";
    return mp(Domain(mp)!SymmetricProduct(x,y));
  else
    error "x and y are incompatible with mp, I don't know how to apply it.";
  end if;
end function;

intrinsic IsotypicDecomposition(X::ModGrp) -> SeqEnum
  {
    Return the isotypic decomposition of X.
  }
  T := TrivialModule(Group(X), BaseRing(X));
  D := DirectSumDecomposition(X);
  _,ic := IsomorphismClasses([T] cat D);
  return [ sub<X|D[c]> : c in [[i-1:i in x|i gt 1]], x in ic | #c gt 0 ];
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



// --------------------------------------------
//
//             DecAlg functions
//
// --------------------------------------------
/*

======= DecAlg functions and operations =======

*/
intrinsic Print(A::DecAlg)
  {
  Prints a partial axial algebra.
  }
  printf "A %o-dimensional decomposition algebra with %o decompositions", Dimension(A), #IndexSet(A);
end intrinsic;

intrinsic RemoveDecomposition(~A::DecAlg, i::.)
  {
    Removes decomposition i from A.
  }
  Remove(~(A`decompositions), i);
end intrinsic;

intrinsic RemoveDecomposition(A::DecAlg, i::.) -> DecAlg
  {
    Removes decomposition i from A.
  }
  A := CopyDecompositionAlgebra(A);
  Remove(~(A`decompositions), i);
end intrinsic;

intrinsic RemoveDecompositions(~A::DecAlg, I::.)
  {
    Removes the decompositions in I from A.
  }
  for i in I do
    RemoveDecomposition(~A, i);
  end for;
end intrinsic;

intrinsic RemoveDecompositions(A::DecAlg, I::.) -> DecAlg
  {
    Removes the decompositions in I from A.
  }
  A := CopyDecompositionAlgebra(A);
  for i in I do
    RemoveDecomposition(~A, i);
  end for;
  return A;
end intrinsic;

/*

======= Invariants of an algebra =======

*/
intrinsic CoefficientRing(A::DecAlg) -> Rng
  {
  The coefficient ring (or base ring) of the algebra.
  }
  return BaseRing(A);
end intrinsic;

intrinsic CoefficientField(A::DecAlg) -> Rng
  {
  }
  return BaseRing(A);
end intrinsic;

intrinsic BaseRing(A::DecAlg) -> Rng
  {
  }
  return BaseRing(Algebra(A));
end intrinsic;

intrinsic BaseField(A::DecAlg) -> Rng
  {
  }
  return BaseRing(A);
end intrinsic;

intrinsic Dimension(A::DecAlg) -> RngIntElt
  {
  Dimension of the algebra.
  }
  return Dimension(Algebra(A));
end intrinsic;

intrinsic FusionLaw(A::DecAlg) -> FusLaw
  {
    Returns the fusion law for A.
  }
  return A`fusion_law;
end intrinsic;

intrinsic Algebra(A::DecAlg) -> Alg
  {
    Returns the underlying algebra for A.
  }
  return A`algebra;
end intrinsic;

intrinsic VectorSpace(A::DecAlg) -> Alg
  {
    Returns the underlying algebra for A.
  }
  return VectorSpace(Algebra(A));
end intrinsic;

intrinsic Decompositions(A::DecAlg) -> Assoc
  {
    Returns the decompositions of A as an associative array.
  }
  return A`decompositions;
end intrinsic;

intrinsic IndexSet(A::DecAlg) -> Set
  {
    Returns the set indexing the decompositions.
  }
  return Keys(A`decompositions);
end intrinsic;

/*

======= Functions on a subalgebra =======

*/
intrinsic Hash(A::DecAlg) -> RngIntElt
  {
  Returns the hash value for A.
  }
  return Hash(<Algebra(A), Decompositions(A)>);
end intrinsic;

intrinsic 'eq'(A::DecAlg, B::DecAlg) -> BoolElt
  {
  Returns whether A equals B.
  }
  return Algebra(A) eq Algebra(B) and Decompositions(A) eq Decompositions(B);
  // NB, this checks the fusion law too as the keys of the decomposition are FusLawElts.
end intrinsic;

/*

======= Creating DecAlgs =======

*/
intrinsic CopyDecompositionAlgebra(A::DecAlg) -> DecAlg
  {
    Create a copy of A.
  }
  if ISA(Type(A), AxlDecAlg) then
    Anew := New(AxlDecAlg);
    axl := true;
  else
    Anew := New(DecAlg);
    axl := false;
  end if;
  fus := FusionLaw(A); Anew`fusion_law := fus;
  alg := Algebra(A); Anew`algebra := alg;
  vs := VectorSpace(Anew);
  IS := [i : i in IndexSet(A)];
  bases := [ [ Basis(Part(Decompositions(A)[i], x)) : 
               x in Elements(fus) ] : i in IS ];
  if axl then
    axes := [ Vector(Eltseq(Axis(Decompositions(A)[i]))) : i in IS ];
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
    decs[IS[i]] := Dnew;
  end for;
  Anew`decompositions := decs;
  return Anew;
end intrinsic;

intrinsic StandardCopy(A::DecAlg) -> DecAlg
  {
    Create a copy of A with decompositions index by the integers.
  }
  if ISA(Type(A), AxlDecAlg) then
    Anew := New(AxlDecAlg);
    axl := true;
  else
    Anew := New(DecAlg);
    axl := false;
  end if;
  fus := FusionLaw(A); Anew`fusion_law := fus;
  alg := Algebra(A); Anew`algebra := alg;
  vs := VectorSpace(Anew);
  IS := [i : i in IndexSet(A)];
  bases := [ [ Basis(Part(Decompositions(A)[i], x)) : 
               x in Elements(fus) ] : i in IS ];
  neworder := [1..#IS];
  if axl then
    axes := [ Vector(Eltseq(Axis(Decompositions(A)[i]))) : i in IS ];
    ParallelSort(~bases, ~neworder);
    Reverse(~bases);
    Reverse(~neworder);
    axes := axes[neworder];
  else
    ParallelSort(~bases, ~neworder);
    Reverse(~bases);
    Reverse(~neworder);
  end if;
  oldidx := IS[neworder];
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
  return Anew, oldidx;
end intrinsic;

intrinsic DecompositionAlgebra(A::ParAxlAlg) -> DecAlg
  {
  Creates a decomposition algebra from a partial axial algebra.
  }
  Anew := New(DecAlg);
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
      D := Decomposition(Anew, S);
      Append(~decs, D);
    end for;
  end for;
  
  Anew`decompositions := AssociativeArray([* <i, decs[i]> : i in [1..#decs]*]);
  
  return Anew;
end intrinsic;

/*

======= Creating specific elements =======

*/
intrinsic Zero(A::DecAlg) -> DecAlgElt
  {
  Creates the zero element of A.
  }
  return CreateElement(A, Zero(Algebra(A)));
end intrinsic;

intrinsic HasOne(A::DecAlg) -> BoolElt, DecAlgElt
  {
  Does the algebra have an identity?  If so, also return the identity.
  }
  so, A1 := HasOne(Algebra(A));
  if so then
    return true, CreateElement(A, A1);
  else
    return false, _;
  end if;
end intrinsic;

intrinsic One(A::DecAlg) -> DecAlgElt
  {
  Creates the identity element of A, if it exists.  Otherwise an error occurs.
  }
  so, A1 := HasOne(A);
  require so: "The algebra has no identity element.";
  return A1;
end intrinsic;

intrinsic Basis(A::DecAlg) -> SeqEnum[DecAlgElt]
  {
  Returns a basis of the decomposition algebra A.
  }
  return ChangeUniverse(Basis(Algebra(A)), A);
end intrinsic;

intrinsic BasisElement(A::DecAlg, i::RngIntElt) -> DecAlgElt
  {
  The ith basis element of the decomposition algebra A.
  }
  return A!BasisElement(Algebra(A), i);
end intrinsic;

intrinsic '.'(A::DecAlg, i::RngIntElt) -> DecAlgElt
  {
  }
  return BasisElement(A, i);
end intrinsic;

intrinsic IsIndependent(S::[DecAlgElt]) -> BoolElt
  {
  Given a sequence S of decomposition algebra elements, return whether they are linearly independent.
  }
  A := Universe(S);
  return IsIndependent([ Algebra(A) | Eltseq(x) : x in S]);
end intrinsic;

// Can also do ExtendBasis for subalgebras, when we have done subalgebras
intrinsic ExtendBasis(S::[DecAlgElt], A::DecAlg) -> SeqEnum[DecAlgElt]
  {
  Extends S to a basis of the decomposition algebra A.
  }
  A := Universe(S);
  require IsIndependent(S): "The sequence of elements given is not linearly independent.";
  return ChangeUniverse(ExtendBasis([ Algebra(A) | Eltseq(x) : x in S], Algebra(A)), A);
end intrinsic;
// --------------------------------------------
//
//             DecAlgElt functions
//
// --------------------------------------------
/*

======= DecAlgElt functions and operations =======

*/
intrinsic Parent(x::DecAlgElt) -> DecAlg
  {
    Return the parent of x.
  }
  return x`parent;
end intrinsic;

// Should we also/instead define elementtosequence?
intrinsic Eltseq(x::DecAlgElt) -> SeqEnum
  {
    Returns the elements of x as a sequence.
  }
  return Eltseq(x`elt);
end intrinsic;

intrinsic Print(x::DecAlgElt)
  {
    Prints x.
  }
  printf "%o", x`elt;
end intrinsic;

intrinsic Hash(x::DecAlgElt) -> RngIntElt
  {
    Returns the hash value for x.
  }
  return Hash(Eltseq(x));
end intrinsic;

// I had this as an intrinsic before, but maybe a function is better??
function CreateElement(A, x)
  xx := New(DecAlgElt);
  xx`parent := A;
  xx`elt := (A`algebra)!x;
  
  return xx;
end function;

intrinsic IsCoercible(A::DecAlg, x::.) -> BoolElt, .
  {
  Returns whether x is coercible into A and the result if so.
  }
  if Type(x) eq RngIntElt and x eq 0 then
    return true, Zero(A);
  elif Type(x) eq RngIntElt and x eq 1 then
    so, A1 := HasOne(A);
    if so then
      return so, A1;
    end if;
  elif ISA(Type(x), DecAlgElt) and x`parent eq A then
    return true, x;
  elif ISA(Type(x), AlgElt) and x in Algebra(A) then
    return true, CreateElement(A, x);
  elif ISA(Type(x), ModTupFldElt) and x in VectorSpace(A) then
    return true, CreateElement(A, x);
  elif ISA(Type(x), SeqEnum) then
    ae := Algebra(A)!x;
    return true, CreateElement(A, x);
  // More to add here!!
  end if;
  return false, "Illegal coercion.";
end intrinsic;

intrinsic Vector(v::DecAlgElt) -> ModTupRngElt
  {
  Returns v as an element of the vector space.
  }
  return VectorSpace(Parent(v))!Eltseq(v);
end intrinsic;

/*

======= Operations on the elements =======

*/
intrinsic '-'(x::DecAlgElt) -> DecAlgElt
  {
    Returns the negation of x.
  }
  return CreateElement(Parent(x), -x`elt);
end intrinsic;

intrinsic '+'(x::DecAlgElt, y::DecAlgElt) -> DecAlgElt
  {
    Returns the sum of x and y.
  }
  require Parent(x) eq Parent(y): "x and y are not in the same decomposition algebra.";
  return CreateElement(Parent(x), x`elt+y`elt);
end intrinsic;

intrinsic '-'(x::DecAlgElt, y::DecAlgElt) -> DecAlgElt
  {
    Returns the difference of x and y.
  }
  require Parent(x) eq Parent(y): "x and y are not in the same decomposition algebra.";
  return CreateElement(Parent(x), x`elt-y`elt);
end intrinsic;

intrinsic '*'(x::DecAlgElt, y::DecAlgElt) -> DecAlgElt
  {
    Returns the product of x and y.
  }
  require Parent(x) eq Parent(y): "x and y are not in the same decomposition algebra.";
  return CreateElement(Parent(x), x`elt*y`elt);
end intrinsic;

intrinsic '*'(r::RngElt, x::DecAlgElt) -> DecAlgElt
  {
    Returns the scalar product of r and x.
  }
  require r in BaseRing(Parent(x)): "The scalar given is not in the base ring of the algebra.";
  return CreateElement(Parent(x), r*x`elt);
end intrinsic;

intrinsic '*'(x::DecAlgElt, r::RngElt) -> DecAlgElt
  {
  }
  return r*x;
end intrinsic;

intrinsic '/'(x::DecAlgElt, r::RngElt) -> DecAlgElt
  {
    Returns the scalar division of x by r.
  }
  R := BaseRing(Parent(x));
  require r in R: "The scalar given is not in the base ring of the algebra.";
  so, rinv := IsInvertible(R!r);
  require so: "The scalar is not invertible.";
  return CreateElement(Parent(x), rinv*x`elt);
end intrinsic;
 
intrinsic '*'(x::DecAlgElt, g::GrpElt) -> DecAlgElt
  {
    Returns the image of x under the action of g.
  }
  A := Parent(x);
  if Parent(g) eq UniversalMiyamotoGroup(A) then
    g := A`universal_projection(g);
  end if;
  if Parent(g) eq MiyamotoGroup(A) then
    mtrx := MiyamotoAction(A, g);
    return A!(Vector(Eltseq(x))*Matrix(mtrx));
  end if;
  error "%o is not in the (Universal) Miyamoto group.";
end intrinsic;
/*

======= Comparisons and Membership for the elements =======

*/
intrinsic 'eq'(x::DecAlgElt, y::DecAlgElt) -> BoolElt
  {
    Returns whether x equals y.
  }
  require Parent(x) eq Parent(y): "The two elements are not in the same decomposition algebra.";
  return Eltseq(x) eq Eltseq(y);
end intrinsic;

intrinsic 'in'(x::DecAlgElt, A::DecAlg) -> BoolElt
  {
    Returns whether x is in A.
  }
  return Parent(x) eq A;
end intrinsic;

// NB, we get ne and notin for free
/*

======= Predicates for the elements =======

*/
intrinsic IsZero(x::DecAlgElt) -> BoolElt
  {
    Returns whether x is the zero element.
  }
  return IsZero(x`elt);
end intrinsic;

intrinsic IsOne(x::DecAlgElt) -> BoolElt
  {
    Returns whether x is the identity for the algebra.
  }
  return IsOne(x`elt);
end intrinsic;

intrinsic IsMinusOne(x::DecAlgElt) -> BoolElt
  {
    Returns whether x is minus the identity for the algebra.
  }
  return IsMinusOne(x`elt);
end intrinsic;

intrinsic IsNilpotent(x::DecAlgElt) -> BoolElt, RngIntElt
  {
    Returns whether x is nilpotent.  That is, if x^n = 0 for some n \geq 0.  If true, also returns the minimal such n.
  }
  return IsNilpotent(x`elt);
end intrinsic;

intrinsic IsIdempotent(x::DecAlgElt) -> BoolElt
  {
    Returns whether x is idempotent.
  }
  return IsIdempotent(x`elt);
end intrinsic;
// --------------------------------------------
//
//                Dec functions
//
// --------------------------------------------
/*

======= Dec functions and operations =======

"*/
intrinsic Print(D::Dec)
  {
  Prints a decomposition.
  }
  printf "Decomposition of a %o-dimensional algebra into %o parts: %o", 
    Dimension(Parent(D)), NumberOfParts(D), 
    [ Dimension(Part(D,i)) : i in Elements(FusionLaw(D)) ];
end intrinsic;

intrinsic Hash(D::Dec) -> RngIntElt
  {
  Returns the hash value for D.
  }
  return Hash(D`parts);
end intrinsic;

intrinsic 'eq'(D1::Dec, D2::Dec) -> BoolElt
  {
  Returns whether D1 equals D2.
  }
  return D1`parts eq D2`parts;
end intrinsic;

intrinsic Parent(D::Dec) -> .
  {
    Returns the algebra for which D is a decomposition.
  }
  return D`parent;
end intrinsic;

intrinsic IsAttached(D::Dec) -> BoolElt
  {
  Is the decomposition attached to a decomposition algebra?
  }
  return ISA(Type(D`parent), DecAlg);
end intrinsic;

intrinsic FusionLaw(D::Dec) -> FusLaw
  {
    Returns the fusion law for D.
  }
  return D`fusion_law;
end intrinsic;

intrinsic ComputeFusionLaw(D::Dec) -> FusLaw
  {
  Computes the fusion law for the decomposition.  Note that the fusion law saved for the decomposition should contain the computed one as a sublaw.
  }
  require IsAttached(D): "The decomposition is not attached to an algebra.";
  A := Parent(D);
  
  nparts := NumberOfParts(D);
  parts := [ Part(D,i) : i in [1..nparts]];

  bas := [ Basis(U) : U in parts];
  V := VectorSpaceWithBasis(&cat(bas));
  
  dimseq := Partition([1..Dimension(A)], [Dimension(U) : U in parts]);
  dimseqold := [ [f..f+Dimension(parts[i])-1] where f := i eq 1 select 1 else Self(i-1)[#Self(i-1)]+1 : i in [1..nparts]];
  assert dimseq eq dimseqold;

  function Indicator(v)
    coords := Coordinates(V, V!Eltseq(v));
    return {@ i : i in [1..nparts] | not IsZero(coords[dimseq[i]]) @};
  end function;

  FL := New(FusLaw);
  FL`set := IndexedSet([1..nparts]);
  
  FL`law := [[ {@ Universe(FL`set)| @} : i in [1..nparts] ] : i in [1..nparts] ];
  
  for i in [1..nparts] do
    if IsCommutative(A) then
      for j in [i..nparts] do
        prods := [ (A!v)*(A!w) : v in bas[i], w in bas[j]];
        FL`law[i,j] := &join[ Indicator(p) : p in prods];
        FL`law[j,i] := FL`law[i,j];
      end for;
    else
      // we are not commutative
      for j in [1..nparts] do
        prods := [ (A!v)*(A!w) : v in bas[i], w in bas[j]];
        FL`law[i,j] := &join[ Indicator(p) : p in prods];
      end for;
    end if;
  end for;

  if IsAxial(D) then
    a := A!Axis(D);
    vects := [ Rep(U) : U in parts ];
    av := [ a*A!v : v in vects ];
    eigenvalues := [ av[i, r]/vects[i, r] where r is Rep(Support(vects[i])) : i in [1..nparts]];
    f := map< FL`set -> BaseRing(A) | i:->eigenvalues[i], j:-> Position(eigenvalues,j)>;
    AssignEvaluation(~FL, f);
  end if;

  return FL;
end intrinsic;

// Can we implement the following using [] notation
intrinsic Part(D::Dec, x::FusLawElt) -> ModTupRng
  {
    Returns the part of D for the fusion law element x.
  }
  if not IsDefined(D`parts, x) then
    D`parts[x] := sub<VectorSpace(Parent(D))|>;
  end if;
  return D`parts[x];
end intrinsic;

intrinsic Part(D::Dec, X::SetIndx[FusLawElt]) -> ModTupRng
  {
    Return the sum of parts of D for the fusion law elements in X.
  }
  return &+[ Part(D,x) : x in X ];
end intrinsic;

intrinsic NumberOfParts(D::Dec) -> RngIntElt
  {
    Returns the number of parts in decomposition D.
  }
  return #D`parts;
end intrinsic;
intrinsic Nparts(D::Dec) -> RngIntElt
  {
  }
  return NumberOfParts(D);
end intrinsic;

intrinsic Label(D::Dec) -> .
  {
    Returns the label of an attached decomposition D.
  }
  error if not IsAttached(D), "D is not attached.";
  P := Parent(D);
  for l in IndexSet(P) do
    if D eq Decomposition(P, l) then
      return l;
    end if;
  end for; 
  error "Cannot find label for D.";
end intrinsic;

intrinsic Decomposition(A::DecAlg, S::{@ModTupRng@}: labels := func<U|FusionLaw(A)!Position(S, U)>) -> Dec
  {
  Given a set of subspaces S of a decomposition algebra A, creates a Decompositon for A with respect to S.  Optional parameter of label gives the labeling of elements of S; the default is by order in S.
  }
  require IsIndependent(&cat[ Basis(U) : U in S]): "The subspaces given are not a direct sum.";
  require &+S eq VectorSpace(Algebra(A)): "The subspaces given do not span A";
  
  D := New(Dec);
  D`parent := A;
  D`fusion_law := A`fusion_law;
  D`parts := AssociativeArray([* < U@labels, U> : U in S *]);
  
  return D;
end intrinsic;

intrinsic MiyamotoElement(D::Dec, x::AlgChtrElt) -> GrpElt
  {
    Returns the Miyamoto element for character x.
  }
  // NOT YET IMPLMENTED
  // return Null;
end intrinsic;

intrinsic DecompositionSubgroup(D::Dec) -> Grp
  {
    Returns the full decomposition subgroup of D.
  }
  // NOT YET IMPLMENTED
  // return Null;
end intrinsic;

intrinsic DecompositionSubgroup(D::Dec, Y::SetEnum[AlgChtrElt]) -> Grp
  {
    Returns the decomposition subgroup of D generated by the Miyamoto elements
    associated to the characters in Y.
  }
  // NOT YET IMPLMENTED
  // return Null;
end intrinsic;

intrinsic DecompositionSubgroup(D::Dec, Y::SeqEnum[AlgChtrElt]) -> Grp
  {
    Returns the decomposition subgroup of D generated by the Miyamoto elements
    associated to the characters in Y.
  }
  // NOT YET IMPLMENTED
  // return Null;
end intrinsic;

intrinsic IsAxial(D::Dec) -> BoolElt
  {
    Returns if the decomposition is axial
  }
  if ISA(Type(D), AxlDec) then
    return true;
  end if;
  return false;
end intrinsic;
// --------------------------------------------
//
//         Axial Decomposition Algebras
//
// --------------------------------------------
/*

======= The following are axial versions inheriting the structures above =======

*/
//Probably the following declaration is wrong.
declare type AxlDecAlgElt: DecAlgElt;

declare type AxlDecAlg[AxlDecAlgElt]: DecAlg;

declare type AxlDec: Dec;

declare attributes AxlDec:
  axis;         // An (Axl)DecAlgElt

/*

======= AxlDecAlg functions and operations =======

*/
intrinsic Print(A::AxlDecAlg)
  {
  Prints a partial axial algebra.
  }
  printf "A %o-dimensional axial decomposition algebra with %o decompositions", Dimension(A), #IndexSet(A);
end intrinsic;

intrinsic Axes(A::AxlDecAlg) -> SetIndx[AxlDecAlgElt]
  {
    Returns the set of axes for A.
  }
  return {@ Axis(Decompositions(A)[k]) : k in IndexSet(A) @};
end intrinsic;

intrinsic AxialDecompositionAlgebra(A::ParAxlAlg) -> DecAlg
  {
  Creates an axial decomposition algebra from a partial axial algebra.
  }
  Anew := New(AxlDecAlg);
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

  return sc where sc is StandardCopy(RemoveDuplicateDecompositions(A));
end intrinsic; 



/*

======= AxlDecAlgElt functions and operations =======

*/

/*
 * AxlDec functions and operations
 */
intrinsic Axis(D::AxlDec) -> .
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
  Given a set of subspaces S of a decomposition algebra A, creates a Decompositon for A with respect to S.  Optional parameter of label gives the labeling of elements of S; the default is by order in S.
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
