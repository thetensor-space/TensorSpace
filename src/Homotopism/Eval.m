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



// ------------------------------------------------------------------------------
//                                   Evaluation
// ------------------------------------------------------------------------------
intrinsic '@'( t::TenSpcElt, H::Hmtp ) -> TenSpcElt
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

    for a in [0..v-1] do
      sc := __Apply(sc, dims, H.a, a);
    end for;

  try
    for a in [0..v-1] do
      sc := __Apply(sc, dims, H.a, a);
    end for;
  catch err
    error "Cannot apply given homotopism.";
  end try;

  new_dims := [Dimension(Domain(H.a)) : a in [v-1..0 by -1]];
  
  return Tensor(new_dims, sc, t`Cat);
end intrinsic;
