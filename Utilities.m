/*

Some handy Magma utilities.

NB some of these may make questionable choices.

*/
/*

======= Hash functions for Lists and tuples =======

*/
intrinsic Hash(T::Tup) -> RngIntElt
  {
  }
  try
    return &+[Hash(t) : t in T];
  catch e
    return 1;
  end try;
end intrinsic;

intrinsic Hash(T::List) -> RngIntElt
  {
  }
  try
    return &+[Hash(t) : t in T];
  catch e
    return 1;
  end try;
end intrinsic;
/*

======= Functions for associative arrays =======

*/
intrinsic Hash(A::Assoc) -> RngIntElt
  {
  }
  try
    return &+[ Hash(<k, A[k]>) : k in Keys(A)];
  catch e
    return 1;
  end try;
end intrinsic;

intrinsic 'eq'(A::Assoc, B::Assoc) -> BoolElt
  {
  Equality for AssociativeArrays.
  }
  return (Universe(A) cmpeq Universe(B)) and (Keys(A) eq Keys(B)) and forall{ k : k in Keys(A) | A[k] cmpeq B[k] };
end intrinsic;

intrinsic AssociativeArray(x::List) -> Assoc
  {
  Convert a list of pairs into an associative array.
  }
  A := AssociativeArray();
  for p in x do
    require #p eq 2 : "Ill—formed pair in AssociativeArray";
    A[p[1]] := p[2];
  end for;
  return A;
end intrinsic;
/*

======= Functions on sets and sorting =======

*/
function lenlex_sort(x,y)
  if #x-#y ne 0 then
    return #x-#y;
  elif x eq y then
    return 0;
  else
    try
      assert exists(i){i : i in [1..#x] | x[i] ne y[i]};
      return x[i] lt y[i] select -1 else 1;
    catch e;
      return 0; // If we can't compare, then select 0;
    end try;
  end if;
end function;

intrinsic Subsets(S::SetIndx:empty := true) -> SetIndx
  {
  Returns the subsets of S ordered by length and lexicographically wrt S.
  }
  S_Sort := func<x,y | Position(S, x) - Position(S, y)>;
  function sub_Sort(x,y)
    if #x-#y ne 0 then
      return #x-#y;
    elif x eq y then
      return 0;
    else
      assert exists(i){i : i in [1..#x] | x[i] ne y[i]};
      return Position(S, x[i]) - Position(S, y[i]);
    end if;
  end function;
  
  subsets := Subsets(Set(S));
  if not empty then
    subsets diff:= {{}};
  end if;
  
  return Sort({@ Sort(IndexedSet(T), S_Sort) : T in subsets @}, sub_Sort);
end intrinsic;
