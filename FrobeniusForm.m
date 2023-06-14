/*

=========== Code to find Frobenius form =============

Here we will represent products of axes by tuples

eg <1,<2,3>> represents a_1*(a_2*a_3)

*/
/*

For a bracketed expression eg <1,<2,3>>, return which shell it is in ie how many products are needed.

*/
function ShellLength(L)
  if Type(L) eq RngIntElt then
    return 1;
  else
    return ShellLength(L[1])+ ShellLength(L[2]);
  end if;
end function;
/*

Given two bracketed expresions, L and M, move products from one to the other, as in a Frobenius form, until one expresion is a number (representing an axis).

*/
function ShiftProducts(L, M)
  // if L is a bracket, then we shift
  while Type(L) eq Tup and #L eq 2 do
    M := < L[2], M >;
    L := L[1];
  end while;
  // now L must be an integer
  
  return L, M;
end function;
/*

Normalise a tuple representing a product

*/
function NormaliseTup(L)
  if Type(L) eq RngIntElt then
    return L;
  end if;
  // if L is a single product eg L = <i,j>
  if Type(L[1]) eq Type(L[2]) and Type(L[1]) eq RngIntElt then
    if L[1] le L[2] then return L;
    else return <L[2], L[1]>;
    end if;
  end if;
  // Otherwise L is a nested product, so recurse.
  if ShellLength(L[2]) lt ShellLength(L[1]) then
    L := < L[2], L[1] >;
  end if;
  return < NormaliseTup(L[1]), NormaliseTup(L[2])>;
end function;
/*

Find a product of a bracket L and axes are the axes.

*/
function EvaluateBracket(axes, L)
  if Type(L) eq RngIntElt then
    return axes[L];
  else
    assert Type(L) eq Tup and #L eq 2;
    return EvaluateBracket(axes, L[1])*EvaluateBracket(axes, L[2]);
  end if;
end function;
/*

Given a basis of a subspace and some extra vectors sieve the extra vectors to form a basis of the space spanned by all vectors

*/
function CompleteToBasis(bas, extra)
  // note from before suggest working in a quotient is quicker.
  V := Universe(bas);
  U := sub<V | bas >;
  Q, quo := quo<V | bas>;
  
  extra_Q := extra@quo;
  dim := Dimension(sub<Q | extra_Q>);
  extra_bas := [];
  index := [];
  
  i := 0;
  while #extra_bas ne dim do
    i +:= 1;
    if IsIndependent(extra_bas cat [extra_Q[i]]) then
      Append(~extra_bas, extra_Q[i]);
      Append(~index, i);
    end if;
  end while;
  
  return index;
end function;
/*

Given a sequence of product tuples < < product >, v>, dedupe it.

*/
procedure Dedupe(~L)
  try
    // dedupe the tuples using magma's internal functions
    Ltups := {@ t[1] : t in L @};
    // Now rebuild the list
    L := [* < tt, v> where so := exists(v){l[2] : l in L | l[1] eq tt} : tt in Ltups *];
  catch e
    out := [**];
    // build hashes
    hashes := { Hash(l) : l in L};
    outhash := {};
    for l in L do
      lhash := Hash(l);
      if lhash notin outhash then
        Include(~outhash, lhash);
        Append(~out,l);
      else
        if not exists{ k : k in out | k cmpeq l} then
          Append(~out,l);
        end if;
      end if;
    end for;
    L := out;
  end try;
end procedure;

intrinsic ShellBasis(A::AxlAlg) -> List, List
  {
  We define the mth shell of A as being the subspace spanned by all elements which can be written as a product of at most m axes (with any bracketing).
  
  This returns a List of pairs, the first element is a tuples eg < 1, < 2,3>>, which represent the product a_1(a_2 a_3), where a_i is the ith axis of A, and the second element is the product.
  }
  require IsCommutative(A): "This version just works for a commutative algebra.";
  /*
  Since multiplication is bilinear, we can obtain a basis for the kth shell in the following way:
  
    1) For each i<k, multiply a basis for the ith shell by a basis for the (k-i)th shell
    2) Sieve these vectors to obtain a linearly independent set
  
  So at each stage we can store just a basis for the products we compute.  
  */
  W := VectorSpace(A);
  axes := Axes(A);
  
  // If ShellLength is slow, could instead store as a SeqEnum of Assocs where the kth Assoc is products in the kth but not the (k-1)th shell.
  // Store shell as a list of lists
  all_shell := [* <i, axes[i]> : i in [1..#axes]*];
  shell := [ all_shell ];
  
  bas := [ Vector(p[2]) : p in shell[1] ];
  m := 1;
  while #bas ne Dimension(W) do
    m +:=1;
    // Multiplication is commutative, so we just need to do all pairs up to half the dimension
    // Could be fancier about doing bulk multiplication here
    newshell := [* < NormaliseTup(<p[1], q[1]>), p[2]*q[2]> : p in shell[i], q in shell[m-i], i in [1..Floor(m/2)] *];
    
    // Dedupe
    Dedupe(~newshell);
    
    // add all the new shell to all_shell
    all_shell cat:= newshell;
    
    // We don't yet have a basis, so we sieve to add basis elements
    extra := [ Vector(p[2]) : p in newshell];
    index := CompleteToBasis(bas, extra);
    bas cat:= extra[index];
    
    // update shell
    Append(~shell, newshell[index]);
  end while;
  
  return &cat shell, all_shell;
end intrinsic;

intrinsic HasFrobeniusForm(A::AxlAlg) -> BoolElt, AlgMatElt
  {
  Computes whether an axial algebra has a Frobenius form, is so returns a Boolean and the Gram matrix of the form.
  }
  if assigned A`Frobenius_form then
    return true, A`Frobenius_form;
  end if;
  
  require IsCommutative(A): "The algebra must be commutative";
  
  bas, _ := ShellBasis(A);
  
  axes := {@ p[2] : p in bas | Type(p[1]) eq RngIntElt @};
  
  // Precompute vector spaces for each axis to speed up projection step
  Vs := [];
  for i in [1..#axes] do
    dec := Decomposition(axes[i]);
    so := exists(P){ P : P in Parts(dec) | Vector(axes[i]) in P};
    assert so; // The axis is by definition in some part
  
    require Dimension(P) eq 1: "The axis is not primitive";
    V := VectorSpaceWithBasis([Vector(axes[i])] cat &cat[ Basis(U) : U in Parts(dec) | U ne P]);
    Append(~Vs, V);
  end for;
  
  form := [[] : i in [1..#bas]];
  for i in [1..#bas] do
    ib, _ := Explode(bas[i]);
    for j in [1..i] do
      jb, _ := Explode(bas[j]);
      a, L := ShiftProducts(ib, jb);
      v := EvaluateBracket(axes, L);
      form[i,j] := Coordinates(Vs[a], Vector(v))[1]; // We use our precomputed vector spaces
    end for;
  end for;
  form := SymmetricMatrix(&cat form);
  
  // Change basis
  bas_to_std := Matrix([Vector(t[2]) : t in bas])^-1;
  form := bas_to_std*form*Transpose(bas_to_std);
    
  vprint DecAlg, 1: "Checking the form.";
  // To check form just need to check on a basis
  // Fix e_j, we need to check that for all i, k we have (ij,k) = (i,jk)
  // This is equivalent to checking the matrix condition ad_(e_j)*form = form*ad_(e_j)^t
  // Since form is symmetric, form*ad_(e_j)^t = (ad_(e_j)*form)^t
  // So it is enough to check that ad_(e_j)*form is symmetric
  
  if not forall{ i : i in [1..Dimension(A)] | IsSymmetric(AdjointMatrix(A.i)*form) } then
    return false, _;
  end if;
  
  // This could also be checked as a Sylvester problem using kronecker products, but this was much slower for the 46-dim A5
  
  // cache the form for future use
  A`Frobenius_form := form;
  
  return true, A`Frobenius_form;
end intrinsic;

intrinsic FrobeniusForm(A::AxlAlg) -> Mtrx
  {
  Returns the Gram matrix of the form.
  }
  so, form := HasFrobeniusForm(A);
  
  require so: "The axial algebra has no Frobenius form.";
  
  return form;
end intrinsic;

intrinsic Frobenius(a::AxlAlgElt, b::AxlAlgElt) -> FldElt
  {
  returns the value of the Frobenius form (a,b)
  }
  require Parent(a) eq Parent(b): "The elements must be from the same axial algebra";
  so, form := HasFrobeniusForm(Parent(a));
  require so: "The axial algebra has no Frobenius form.";
  
  return InnerProduct(Vector(a)*form, Vector(b));
end intrinsic;
