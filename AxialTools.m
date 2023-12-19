/*

Code for identifying FusionLaws and Miyamoto involutions

NB - requires the AxialTools package

*/
//
//
// ========== Functions to check deompositions ==========
//
//
/*

Adjoint

*/
intrinsic AdjointMatrix(a::DecAlgElt) -> AlgMatElt
  {
  The adjoint matrix for the (right) action of a.
  }
  A := Algebra(Parent(a));
  return AdjointMatrix(A!Eltseq(a));
end intrinsic;
/*

Eigenvalues and Eigenspaces

*/
intrinsic Eigenvalues(a::DecAlgElt) -> SetIndx
  {
  Returns the Eigenvalues for the adjoint action of a.
  }
  A := Algebra(Parent(a));
  return Eigenvalues(A!Eltseq(a));
end intrinsic;

intrinsic Eigenspace(a::DecAlgElt, lm::RngElt) -> ModTupRng
  {
  The lm-eigenspace of the adjoint action of a.
  }
  A := Algebra(Parent(a));
  return Eigenspace(A!Eltseq(a), lm);
end intrinsic;
/*

check semisimplicity

*/
intrinsic IsSemisimple(a::DecAlgElt) -> BoolElt, SeqEnum, SetIndx
  {
  Returns whether the element semisimple.  If true also returns the set of eigenvalues and the eigenspaces.
  }
  A := Algebra(Parent(a));
  return IsSemisimple(A!Eltseq(a));
end intrinsic;
/*

Identify fusion law

*/
intrinsic IdentifyFusionLaw(a::DecAlgElt: eigenvalues := Eigenvalues(a)) -> SetEnum, SeqEnum, FusLaw
  {
  If the element is semisimple, returns the eigenvalues, eigenspaces and fusion law.  Optional argument to provide an indexed set of eigenvalues in the desired order.
  }
  A := Algebra(Parent(a));
  return IdentifyFusionLaw(A!Eltseq(a): eigenvalues := eigenvalues);
end intrinsic;

intrinsic MiyamotoInvolution(a::DecAlgElt, lm::RngElt: check_fusion:= true) -> AlgMatElt
  {
  The Miyamoto involution for the axis a with respect to the eigenspace lm.  Note the fusion law must be graded and lm be in a part which is mapped to an involution.
  
  Option argument to check the fusion law.
  }
  A := Algebra(Parent(a));
  return MiyamotoInvolution(A!Eltseq(a), lm: check_fusion := check_fusion);
end intrinsic;

intrinsic MiyamotoInvolution(a::DecAlgElt) -> AlgMatElt
  {
  The Miyamoto involution for the axis a.  Note the fusion law must be C_2 (or trivially) graded.
  }
  A := Algebra(Parent(a));
  return MiyamotoInvolution(A!Eltseq(a));
end intrinsic;
