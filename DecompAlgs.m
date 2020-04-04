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
  Miyamoto_group,            // 
  universal_Miyamoto_group;  //

declare attributes DecAlgElt:
  parent,                    // A FusLaw
  elt;                       // An element of the algebra

declare type Dec;

declare attributes Dec:
  parent,                    // Either an algebra, or a DecAlg
  fusion_law,                // A Fuslaw
  parts;                     // An Assoc indexed by the elements of the fusion law

/*

======= Additional utility functions =======

*/


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
  printf "A %o-dimensional decomposition algebra with %o% decompositions", Dimension(A), #IndexSet(A);
end intrinsic;


/*

======= Invariants of an algebra =======

*/
intrinsic CoefficientRing(A::DecAlg) -> Rng
  {
  The coefficient ring (or base ring) of the algebra.
  }
  return BaseRing(A`algebra);
end intrinsic;

intrinsic CoefficientField(A::DecAlg) -> Rng
  {
  "
  }
  return CoefficientRing(A);
end intrinsic;

intrinsic BaseRing(A::DecAlg) -> Rng
  {
  "
  }
  return CoefficientRing(A);
end intrinsic;

intrinsic BaseField(A::DecAlg) -> Rng
  {
  "
  }
  return CoefficientRing(A);
end intrinsic;

intrinsic Dimension(A::DecAlg) -> RngIntElt
  {
  Dimension of the algebra.
  }
  return Dimension(A`algebra);
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

intrinsic Decompositions(A::DecAlg) -> Assoc//[Dec]
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

intrinsic Decomposition(A::DecAlg, i::.) -> Dec
  {
    Returns the decomposition of A labeled by i.
  }
  require i in IndexSet(A): "i does not index a decomposition.";
  return A`decompositions[i];
end intrinsic;
/*

======= Creating specific elements =======

*/
intrinsic Zero(A::DecAlg) -> DecAlgElt
  {
  Creates the zero element of A.
  }
  return CreateElement(A, Zero(A`algebra));
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

intrinsic Basis(A::DecAlg) -> [ DecAlgElt ]
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
  "
  }
  return BasisElement(A, i);
end intrinsic;

intrinsic IsIndependent(S::[DecAlgElt]) -> BoolElt
  {
  Given a sequence S of decomposition algebra elements, return whether they are linearly independent.
  }
  return IsIndependent([ Algebra(A) | Eltseq(x) : x in S]);
end intrinsic;

// Can also do ExtendBasis for subalgebras, when we have done subalgebras
intrinsic ExtendBasis(S::[DecAlgElt], A::DecAlg) -> [ DecAlgElt ]
  {
  Extends S to a basis of the decomposition algebra A.
  }
  require IsIndependent(S): "The sequence of elements given is not linearly independent.";
  return ChangeUniverse(ExtendBasis([ Algebra(A) | Eltseq(x) : x in S], Algebra(A)), A);
end intrinsic;
/*

======= Functions for finding a group =======

*/
intrinsic MiyamotoGroup(A::DecAlg) -> Grp
  {
    Returns the full Miyamoto group of A.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic UniversalMiyamotoGroup(A::DecAlg) -> Grp
  {
    Returns the full universal Miyamoto group of A.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic MiyamotoGroup(A::DecAlg, x::AlgChtrElt) -> Grp
  {
    Returns the Miyamoto group of A for the given character x.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic UniversalMiyamotoGroup(A::DecAlg, x::AlgChtrElt) -> Grp
  {
    Returns the universal Miyamoto group of A for the given character x.
  }
  // NOT YET IMPLEMENTED
  // return Null;
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
  if x eq 0 then
    return true, Zero(A);
  elif x eq 1 then
    so, A1 := HasOne(A);
    if so then
      return so, A1;
    end if;
  elif ISA(Type(x), DecAlgElt) and x`parent eq A then
    return true, x;
  elif ISA(Type(x), AlgElt) and x in Algebra(A) then
    return true, CreateElement(A, x);
  // More to add here!!
  end if;
  return false, "Illegal coercion.";
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
  "
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
  // NOT YET IMPLEMENTED
  // return Null;
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
  return IsZero(x`elt));
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
  so, n := IsNilpotent(x`elt);
  return so, n;
end intrinsic;

intrinsic IsIdempotent(x::DecAlgElt) -> BoolElt
  {
    Returns whether x is idempotent.
  }
  return IsIdempotent(x`elt);
end intrinsic;

/*

======= Dec functions and operations =======

*/
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

// Can we implement the following using [] notation
intrinsic Part(D::Dec, x::FusLawElt) -> ModTupRng
  {
    Returns the part of D for the fusion law element x.
  }
  return D`parts[x];
end intrinsic;

intrinsic '[]'(D::Dec, x::FusLawElt) -> ModTupRng
  {
    Returns the part of D for the fusion law element x.
  }
  return D`parts[x];
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
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

/*

======= The following are axial versions inheriting the structures above =======

*/
//Probably the following declaration is wrong.
//declare type AxlDecAlgElt, DecAlgElt;

declare type AxlDecAlg[AxlDecAlgElt]: DecAlg;

declare type AxlDec: Dec;

/*

======= AxlDecAlg functions and operations =======

*/
intrinsic Print(A::AxlDecAlg)
  {
  Prints a partial axial algebra.
  }
  printf "A %o-dimensional axial decomposition algebra with %o% decompositions", Dimension(A), #IndexSet(A);
end intrinsic;

/*
 * AxlDecAlgElt functions and operations
 */

/*
 * AxlDec functions and operations
 */
intrinsic Axis(D::AxlDec) -> .
  {
    Returns the axis for D.
  }
  // NOT YET IMPLMENTED
  // return Null;
end intrinsic;

intrinsic Valuation(D::AxlDec) -> Map
  {
    Returns the valuation for D.
  }
  // NOT YET IMPLMENTED
  // return Null;
end intrinsic;
