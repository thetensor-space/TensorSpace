/* 
    Copyright 2016--2019 Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


import "../Tensor/TensorData.m" : __GetFoliation, __ReverseFoliation;


// s: sequence of field elts, dims: sequence of dimensions for [V_vav, ..., V_0], F: a matrix in End(V_a), a: an int (in {0..vav}).
// The point here is that it takes a (flat) sequence and returns a (flat) sequence.
// Intended to do the minimal amount of slicing in a recursive call.
__Apply := function(s, dims, F, a)
  M := __GetFoliation(s, dims, a);
  N := F*M;
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
  dims := [Dimension(X) : X in Frame(t)];

  D := [*Domain(H.a) : a in [v-1..1 by -1]*];
  C := Codomain(H.0);
  F := function(x)
    y := x;
    for i in [1..#x] do
      y[i] := x[i] @ H.(v-i);
    end for;
    return y @ t @ H.0;
  end function;

  s := Tensor(D, C, F, TensorCategory(t));
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

  // Eventually write a slicing version
  // '@' does not work for general matrices
  HomSpc := Hom(Domain(M), Codomain(M));
  return __BlackBoxApply(t, HomSpc!M, a);
end intrinsic;

/*intrinsic '@'( t::TenSpcElt, H::Hmtp ) -> TenSpcElt
{Returns t @ H.}
  v := Valence(t);
  cohom := {[1 : k in [1..v-1]] cat [-1], [-1 : k in [1..v-1]] cat [1]};
  require Arrows(H`Cat) in cohom : 
    "Homotopism must be in a cohomotopism category, captible with the tensor.";
  dims := [Dimension(X) : X in Frame(t)];
  try
    sc := Eltseq(t);
  catch err
    error "Cannot construct structure constants.";
  end try;

  try
    for a in [0..v-1] do
      sc := __Apply(sc, dims, H.a, a);
    end for;
  catch err
    error "Cannot apply given homotopism.";
  end try;

  new_dims := [Dimension(Domain(H.a)) : a in [v-1..0 by -1]];
  
  return Tensor(new_dims, sc, t`Cat);
end intrinsic;*/
