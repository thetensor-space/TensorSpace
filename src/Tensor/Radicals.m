/* 
    Copyright 2016--2019 Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/



intrinsic Radical( t::TenSpcElt, a::RngIntElt ) -> ModTupRng, Mtrx
{Returns the radical of t in the ath coordinate and a matrix that splits the radical in Va.}
  v := t`Valence;
  require a in {1..v-1} : "Unknown coordinate.";
  require ISA(Type(BaseRing(t)), Fld) : "Radicals only implemented for tensors over fields.";
  if Type(t`Radicals[v - a]) ne RngIntElt then
    return t`Radicals[v - a][1], t`Radicals[v - a][2];
  end if;

  try 
    F := Foliation(t, a);
  catch err
    error "Cannot compute structure constants.";
  end try;

  // Construct the radical
  D := t`Domain[v - a];
  B := Basis(D);
  V := VectorSpace(BaseRing(t), #B);
  vprint TensorSpace, 1 : "Solving linear system " cat IntegerToString(Nrows(F)) \
    cat " by " cat IntegerToString(Ncols(F));
  R := Nullspace(F);
  
  // Construct the matrix
  M := Matrix(Reverse(ExtendBasis(R, Generic(R))));
  t`Radicals[v - a] := <R, M>;
  return R, M;
end intrinsic;

intrinsic Coradical( t::TenSpcElt ) -> ModTupRng, Map
{Returns the coradical of t.}
  if Type(t`Radicals[t`Valence]) ne RngIntElt then
    return t`Radicals[t`Valence][1],t`Radicals[t`Valence][2];
  end if;

  I := Image(t);
  C, pi := t`Codomain/I;
  t`Radicals[t`Valence] := <C, pi>;

  return C, pi;
end intrinsic;

intrinsic Radical( t::TenSpcElt ) -> Tup
{Returns the radical of t.}
  return < Radical(t,i) : i in Reverse([1..#t`Domain]) >;
end intrinsic;
