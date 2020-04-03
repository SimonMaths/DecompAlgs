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
  elt;                       // 

declare type Dec;

declare attributes Dec:
  parent,                    // 
  fusion_law,                //
  parts;                     // An Assoc indexed by the elements of the fusion law

/*
 * Additional utility functions
 */


/*
 * DecAlg functions and operations
 */
intrinsic FusionLaw(A::DecAlg) -> FusLaw
  {
    Returns the fusion law for A.
  }
  return A`fusion_law;
end intrinsic;

intrinsic Decompositions(A::DecAlg) -> Assoc//[Dec]
  {
    Returns the decompositions of A as an associative array.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic Decomposition(A::DecAlg, i::.) -> Dec
  {
    Returns the ith decomposition of A.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic IndexSet(A::DecAlg) -> Set
  {
    Returns the set indexing the decompositions.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic Algebra(A::DecAlg) -> Alg
  {
    Returns the underlying algebra for A.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

/*
 * Additional functions
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
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic Print(x::DecAlgElt)
  {
    Prints x.
  }
  // NOT YET IMPLEMENTED
end intrinsic;

intrinsic 'eq'(x::DecAlgElt, y::DecAlgElt) -> BoolElt
  {
    Returns whether x equals y.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic 'in'(x::DecAlgElt, A::DecAlg) -> BoolElt
  {
    Returns whether x is in A.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic Hash(x::DecAlgElt) -> RngIntElt
  {
    Returns the hash value for x.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

// Should we also/instead define elementtosequence?
intrinsic Eltseq(x::DecAlgElt) -> SeqEnum
  {
    Returns the elements of x as a sequence.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic IsZero(x::DecAlgElt) -> BoolElt
  {
    Returns whether x is the zero element.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic IsIdentity(x::DecAlgElt) -> BoolElt
  {
    Returns whether x is an identity for the algebra.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic IsNilpotent(x::DecAlgElt) -> BoolElt
  {
    Returns whether x is nilpotent.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic IsIdempotent(x::DecAlgElt) -> BoolElt
  {
    Returns whether x is idempotent.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;
/*

======= Operations for the elements =======

*/
intrinsic '-'(x::DecAlgElt) -> DecAlgElt
  {
    Returns the negation of x.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic '+'(x::DecAlgElt, y::DecAlgElt) -> DecAlgElt
  {
    Returns the sum of x and y.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic '-'(x::DecAlgElt, y::DecAlgElt) -> DecAlgElt
  {
    Returns the difference of x and y.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic '*'(x::DecAlgElt, y::DecAlgElt) -> DecAlgElt
  {
    Returns the product of x and y.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic '*'(x::DecAlgElt, y::RngElt) -> DecAlgElt
  {
    Returns the scalar product of x and y.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic '*'(x::RngElt, y::DecAlgElt) -> DecAlgElt
  {
    Returns the scalar product of x and y.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic '/'(x::DecAlgElt, y::RngElt) -> DecAlgElt
  {
    Returns the scalar division of x by y.
  }
  // NOT YET IMPLEMENTED
  // return Null;
end intrinsic;

intrinsic '*'(x::DecAlgElt, g::GrpElt) -> DecAlgElt
  {
    Returns the image of x under the action of g.
  }
  // NOT YET IMPLEMENTED
  // return Null;
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
  return D`group;
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
 * AxlDecAlg functions and operations
 */


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
