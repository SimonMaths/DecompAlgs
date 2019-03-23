/*
 *  Package for decomposition algebras and related structures
 *  Authors: Justin McInroy, Simon F. Peacock
 */

/*
 * These are the base types for decomposition algebras
 */
declare type DecAlg[DecAlgElt];
declare type Dec;

/*
 * Additional utility functions
 */


/*
 * DecAlg operations and functions
 */


/*
 * DecAlgElt operations and functions
 */
intrinsic Parent(x::DecAlgElt) -> DecAlg
  {
    Return the parent of x.
  }
  // NOT YET IMPLEMENTED
  return Null;
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
  return Null;
end intrinsic;

intrinsic 'in'(x::DecAlgElt, A::DecAlg) -> BoolElt
  {
    Returns whether x is in A.
  }
  // NOT YET IMPLEMENTED
  return Null;
end intrinsic;

intrinsic Hash(x::DecAlgElt) -> RngIntElt
  {
    Returns the hash value for x.
  }
  // NOT YET IMPLEMENTED
  return Null;
end intrinsic;

// Should we also/instead define elementtosequence?
intrinsic Eltseq(x::DecAlgElt) -> SeqEnum
  {
    Returns the elements of x as a sequence.
  }
  // NOT YET IMPLEMENTED
  return Null;
end intrinsic;

intrinsic IsZero(x::DecAlgElt) -> BoolElt
  {
    Returns whether x is the zero element.
  }
  // NOT YET IMPLEMENTED
  return Null;
end intrinsic;

intrinsic IsIdentity(x::DecAlgElt) -> BoolElt
  {
    Returns whether x is an identity for the algebra.
  }
  // NOT YET IMPLEMENTED
  return Null;
end intrinsic;

/*
 * Operations for the elements
 */
intrinsic '-'(x::DecAlgElt) -> DecAlgElt
  {
    Returns the negation of x.
  }
  // NOT YET IMPLEMENTED
  return Null;
end intrinsic;

intrinsic '+'(x::DecAlgElt, y::DecAlgElt) -> DecAlgElt
  {
    Returns the sum of x and y.
  }
  // NOT YET IMPLEMENTED
  return Null;
end intrinsic;

intrinsic '-'(x::DecAlgElt, y::DecAlgElt) -> DecAlgElt
  {
    Returns the difference of x and y.
  }
  // NOT YET IMPLEMENTED
  return Null;
end intrinsic;

intrinsic '*'(x::DecAlgElt, y::DecAlgElt) -> DecAlgElt
  {
    Returns the product of x and y.
  }
  // NOT YET IMPLEMENTED
  return Null;
end intrinsic;

intrinsic '*'(x::DecAlgElt, y::RngElt) -> DecAlgElt
  {
    Returns the scalar product of x and y.
  }
  // NOT YET IMPLEMENTED
  return Null;
end intrinsic;

intrinsic '*'(x::RngElt, y::DecAlgElt) -> DecAlgElt
  {
    Returns the scalar product of x and y.
  }
  // NOT YET IMPLEMENTED
  return Null;
end intrinsic;

intrinsic '/'(x::DecAlgElt, y::RngElt) -> DecAlgElt
  {
    Returns the scalar division of x by y.
  }
  // NOT YET IMPLEMENTED
  return Null;
end intrinsic;

intrinsic Parent(x::DecAlgElt) -> DecAlg
  {
    Parent of x.
  }
  // NOT YET IMPLEMENTED
  return Null;
end intrinsic;

intrinsic Parent(x::DecAlgElt) -> DecAlg
  {
    Parent of x.
  }
  // NOT YET IMPLEMENTED
  return Null;
end intrinsic;

intrinsic Parent(x::DecAlgElt) -> DecAlg
  {
    Parent of x.
  }
  // NOT YET IMPLEMENTED
  return Null;
end intrinsic;

intrinsic Parent(x::DecAlgElt) -> DecAlg
  {
    Parent of x.
  }
  // NOT YET IMPLEMENTED
  return Null;
end intrinsic;

/*
 * The following are axial versions inheriting the structures above
 */
//Probably the following declaration is wrong.
//declare type AxlDecAlgElt, DecAlgElt;

declare type AxlDecAlg[AxlDecAlgElt], DecAlg;
declare type AxlDec, Dec;

