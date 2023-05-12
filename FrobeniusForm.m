/*

=========== Code to find Frobenius form =============

*/
/*
function EigenvalueSort(x,y)
  if x eq 1 then
    return -1;
  elif y eq 1 then
    return 1;
  elif x eq 0 then
    return -1;
  elif y eq 0 then
    return 1;
  else
    return x-y;
  end if;
end function;

function ShiftProducts(L,M)
  if Type(L) eq RngIntElt then
    return [*L*],M;
  end if;
  while #L eq 2 do
    M := [* L[2], M *];
    if Type(L[1]) ne RngIntElt then
      L := L[1];
    else
      L := [*L[1]*];
    end if;
  end while;
  return L, M;
end function;
    
function NestedDepth(L)
  if Type(L) eq RngIntElt then
    return 0;
  else
    return Max(NestedDepth(L[1]), NestedDepth(L[2]))+1;
  end if;
end function;
    
function RecursiveSort(L)
  if Type(L) eq RngIntElt then
    return L;
  end if;
  if Type(L[1]) eq Type(L[2]) and Type(L[1]) eq RngIntElt then
    if L[1] le L[2] then return L;
    else return [*L[2], L[1]*];
    end if;
  end if;
  if NestedDepth(L[2]) lt NestedDepth(L[1]) then
    L := [* L[2], L[1] *];
  end if;
  return [* RecursiveSort(L[1]), RecursiveSort(L[2])*];
end function;



function FindProduct(A, prods, L)
  // assume that prods is a list of the products up to length m
  if Type(L) eq RngIntElt then
    return prods[1,L,2];
  end if;
  m := #prods;
  d := mLength(L);
  L := RecursiveSort(L);
  if d lt m then
    // we have already calculated this product
    assert exists(v){ prods[d,k,2] : k in [1..#prods[d]] | L eq prods[d,k,1]};
    return v;
  else
    x := FindProduct(A, prods, L[1]);
    y := FindProduct(A, prods, L[2]);
    return (A!x*A!y)`elt;
  end if;
end function;

function Dedupe(L)
  out := [];
  // build hashes
  hashes := { Hash(l) : l in L};
  outhash := {};
  for l in L do
    lhash := Hash(l);
    if lhash notin outhash then
      Include(~outhash, lhash);
      Append(~out,l);
    else
      if l notin out then
        Append(~out,l);
      end if;
    end if;
  end for;
  return out;
end function;
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

Find a product of a bracket L, where shell is a complete list of products up to a given length and A is the algebra.

*/
function FindProduct(A, shell, L)
  axes_shell := [ p : p in shell | Type(p[1]) eq RngIntElt];
  
  if Type(L) eq RngIntElt then
    so := exists(v){p[2] : p in axes_shell | p[1] eq L};
    assert so;
    return v;
  end if;
  
  m := Max({ ShellLength(p[1]) : p in shell});
  // assume all products of length up to m are in shell
  
  if ShellLength(L) lt m then
    // we have already calculated this product
    assert exists(v){ shell[k,2] : k in [1..#shell] | L eq shell[k,1]};
    return v;
  else
    // recurse
    x := FindProduct(A, shell, L[1]);
    y := FindProduct(A, shell, L[2]);
    return x*y;
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
  all_shell := [* <i, axes[i]> : i in [1..#axes]*];
  shell := all_shell;
    
  function shellnum(m)
    return [* p : p in shell | ShellLength(p[1]) eq m *];
  end function;
  
  bas := [ Vector(p[2]) : p in shell ];
  m := 1;
  while #bas ne Dimension(W) do
    m +:=1;
    // Multiplication is commutative, so we just need to do all pairs up to half the dimension
    // Could be fancier about doing bulk multiplication here
    newshell := [* < <p[1], q[1]>, p[2]*q[2]> : p in shellnum(i), q in shellnum(m-i), i in [1..Floor(m/2)] *];
    
    // add all the new shell to all_shell
    all_shell cat:= newshell;
    
    // Now sieve these to find a basis
    extra := [ Vector(p[2]) : p in newshell];
    index := CompleteToBasis(bas, extra);
    bas cat:= extra[index];
    
    // update shell
    shell cat:= newshell[index];
  end while;
  
  return shell, all_shell;
end intrinsic;

intrinsic HasFrobeniusForm(A::AxlAlg) -> BoolElt, AlgMatElt
  {
  Computes whether an axial algebra has a Frobenius form, is so returns a Boolean and the Gram matrix of the form.
  }
  if assigned A`Frobenius_form then
    return true, A`Frobenius_form;
  end if;
  
  require IsCommutative(A): "The algebra must be commutative";
  
  bas, shell := ShellBasis(A);
  
  axes := {@ p : p in bas | Type(p[1]) eq RngIntElt @};
  axes := {@ p[2] : p in Sort(axes, func<x,y|x[1]-y[1]>)@}; // in case they are out of order
  
  // could precompute vector spaces for each axis is this is slow
  form := [[] : i in [1..#bas]];
  for i in [1..#bas] do
    ib, ip := Explode(bas[i]);
    for j in [1..i] do
      jb, jp := Explode(bas[j]);
      
      a, L := ShiftProducts(ib, jb);
      v := FindProduct(A, shell, L);
      form[i,j] := Projection(axes[a], v);
    end for;
  end for;
  form := SymmetricMatrix(&cat form);
  
  vprint DecAlg, 1: "Checking the form.";
  // To check form just need to check on a basis
  // Since (i,jk) = (ij,k) implies (k,ji) = (kj,i) just need to check for k \leq i
  
  // precompute the matrices of all the bas[i]*bas[j]
  basmults := [[] : i in [1..#bas]];
  for i in [1..#bas] do
    ib, ip := Explode(bas[i]);
    for j in [1..#bas] do
      jb, jp := Explode(bas[j]);
      basmults[i][j] := Vector(FindProduct(A, shell, <ib,jb>));
    end for;
  end for;
  basmults := [Matrix(M) : M in basmults];
  
  // Now, to check (e_i,e_j*e_k) = (e_i*e_j, e_k), build matrices over i and k

  std_to_bas := Matrix([Vector(t[2]) : t in bas]);
  bas_to_std := std_to_bas^-1;
  
  for j in [1..#bas] do
    if form*Transpose(basmults[j]*bas_to_std) ne basmults[j]*bas_to_std*form then
      return false, _;
    end if;
  end for;
  
  // cache the form for future use
  A`Frobenius_form := bas_to_std*form*Transpose(bas_to_std);
  
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
