/* ==== Helper functions ==== */
// Multiply x and y using the map mp
// if mp looks like it acts on the tensor product of x and y use it that way
// if mp looks like it acts on the symmetric product of x and y use it that way
// otherwise we have an error
procedure check_dim_of_TXorSX(r, c);
  if r eq c*c then
    return;
  elif 2*r eq c*(c+1) then
    return;
  else
    error "Dimensions are incompatible with tensor or symmetric square.";
  end if;
end procedure;

function mult_with_mtrx(x, y, mtrx);
  x := Vector(Eltseq(x));
  y := Vector(Eltseq(y));
  BR := Parent(Rep([Rep(BaseRing(x)),Rep(BaseRing(y)),Rep(BaseRing(mtrx))]));
  x := Vector(BR, x);
  y := Vector(BR, y);
  mtrx := Matrix(BR, mtrx);
  dx := Degree(x);
  dy := Degree(y);
  rm := Nrows(mtrx);
  cm := Ncols(mtrx);

  if rm eq dx*dy then
    return TensorProduct(x,y)*mtrx;
  elif 2*rm eq dx*(dx+1) then
    error if dx ne dy, "x and y are not from the same space.";
    return SymmetricProduct(x,y)*mtrx;
  elif rm eq dx and cm eq dy then
    return x * mtrx * Transpose(Matrix(y));
  else
    error "x and y are incompatible with mtrx, I don't know how to apply it.";
  end if;
end function;

function mult_with_map(x, y, mp);
  //try
    xy := mult_with_mtrx(x, y, MapToMatrix(mp));
  //catch e
  //  xy := mult_with_mtrx(x, y, Matrix(mp));
  //end try;
  return Codomain(mp)!Eltseq(xy);
end function;

function sym_pair_idx(d,ij);
  i := ij[1];
  j := ij[2];
  b,c := Explode(Sort([Integers() | i,j]));
  error if c gt d, "Index out of bounds.";
  c -:= b;
  b -:= 1;
  bb := (d*(d+1) - (d-b)*(d-b+1))/2;
  cc := c + 1;
  idx := Integers()!(bb+cc);
  return idx;
end function;

function tns_pair_idx(d,ij);
  i := ij[1];
  j := ij[2];
  return (i-1)*d+j;
end function;

function sym_idx_pair(d,idx);
  i := 0;
  while idx gt d do
    idx -:= d;
    d -:= 1;
    i +:= 1;
    error if d le 0, "idx out of bounds.";
  end while;
  return <i+1,i+idx>;
end function; 

function tns_idx_pair(d,idx);
  i := (idx-1) div d;
  j := (idx-1) mod d;
  return <i+1,j+1>;
end function;

function sym_trip_idx(d,ijk);
  i := ijk[1];
  j := ijk[2];
  k := ijk[3];
  a,b,c := Explode(Sort([Integers() | i,j,k]));
  error if c gt d, "Index out of bounds.";
  c -:= b;
  b -:= a;
  a -:= 1;
  aa := (d*(d+1)*(d+2) - (d-a)*(d-a+1)*(d-a+2))/6;
  bb := ((d-a)*(d-a+1) - (d-a-b)*(d-a-b+1))/2;
  cc := c + 1;
  idx := Integers()!(aa+bb+cc);
  return idx;
end function;

