/* 
    Copyright 2016--2019 Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


import "../Tensor/TensorData.m" : __GetFoliation, __ReverseFoliation;
import "../Util/Util.m" : __List, __Tuple;


// s: sequence of field elts, dims: sequence of dimensions for [V_vav, ..., V_0], F: a matrix in End(V_a), a: an int (in {0..vav}).
// The point here is that it takes a (flat) sequence and returns a (flat) sequence.
// Intended to do the minimal amount of slicing in a recursive call.
__Apply := function(s, dims, F, a)
  M := __GetFoliation(s, dims, a);
  if a ne 0 then
    N := F*M;
  else
    N := Transpose(Transpose(M)*F);
  end if;
  dims[#dims-a] := Nrows(F);
  new_s := __ReverseFoliation(N, dims, a);
  return new_s;
end function;


__BlackBoxApply := function(t, F, a)
  v := Valence(t);

  Eval := function(x)
    y := x;
    y[v - a] := x[v - a] @ F;
    return y @ t;
  end function;

  Fr := Frame(t);
  Fr[v - a] := Domain(F);

  s := Tensor(Fr, Eval, TensorCategory(t));
  return s;
end function;


// -----------------------------------------------------------------------------
//                                   Evaluation
// -----------------------------------------------------------------------------
intrinsic '@'( t::TenSpcElt, H::Hmtp ) -> TenSpcElt
{Returns t @ H.}
  v := Valence(t);
  cohom := {[1 : k in [1..v-1]] cat [-1], [-1 : k in [1..v-1]] cat [1]};
  require Arrows(H`Cat) in cohom : 
    "Homotopism must be in a cohomotopism category, captible with the tensor.";

  D := [*Domain(H.a) : a in [v-1..1 by -1]*];
  C := Codomain(H.0);

  F := function(x)
    y := __List(x);
    for i in [1..#x] do
      y[i] := x[i] @ H.(v-i);
    end for;
    return __Tuple(y) @ t @ H.0;
  end function;

  s := Tensor(D, C, F, TensorCategory(t));

  if assigned t`CoordImages and forall{M : M in Maps(H) | ISA(Type(M), Mtrx)} 
      then
    dims_new := [Dimension(X) : X in D cat [*C*]];
    dims := [Dimension(X) : X in Frame(t)]; 
    seq := t`CoordImages;
    for i in [1..v] do
      seq := __Apply(seq, dims, H.(v-i), v-i);
      dims[i] := dims_new[i];
    end for;
    s`CoordImages := seq;
  end if;

  return s;
end intrinsic;

intrinsic Precompose( t::TenSpcElt, f::Map, a::RngIntElt ) -> TenSpcElt
{Returns the tensor precomposed with f in coordinate a.}
  require a gt 0 : "Cannot pre-compose in the 0 coordinate.";
  return __BlackBoxApply(t, f, a);
end intrinsic;

intrinsic Precompose( t::TenSpcElt, M::Mtrx, a::RngIntElt ) -> TenSpcElt
{Returns the tensor precomposed with f in coordinate a.}
  require a gt 0 : "Cannot pre-compose in the 0 coordinate.";
  v := Valence(t);

  // '@' does not work for general matrices
  K := BaseRing(M);
  U := VectorSpace(K, Ncols(M));
  V := VectorSpace(K, Nrows(M));
  HomSpc := Hom(U, V);

  s := __BlackBoxApply(t, HomSpc!M, a);

  // Can be VERY expensive to recompute structure constants
  if assigned t`CoordImages then
    dims := [Dimension(X) : X in Frame(t)];
    s`CoordImages := __Apply(Eltseq(t), dims, M, a);
  end if;

  return s;
end intrinsic;
