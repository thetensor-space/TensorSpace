/* 
    Copyright 2016, 2017, Joshua Maglione, James B. Wilson.
    Distributed under GNU GPLv3.
*/


/*
  This file contains functions to construct random (co)tensors.
*/


import "../GlobalVars.m" : __FRAME;


// Meant as a quick check for R, not R^n.
__HasRandom := function( X )
  try 
    B := Random(X);
  catch e
    if assigned e`Object then
      return false;
    end if;
  end try;
  return true;
end function;

// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

intrinsic Random( T::TenSpc ) -> TenSpcElt
{Returns a random element of the finite tensor space T.}
  dims := [ Dimension(M) : M in T`Frame ];
  if exists{ d : d in dims | d eq 0 } then // to fix a bug when one entry is 0
    spaces := __FRAME(T);
    C := spaces[#spaces];
    F := function(x)
      return C!0;
    end function;
    t := Tensor( Frame(T), F, T`Cat );
    t`Parent := T;
    return t;
  end if;
  M := T`Mod;
  try
    m := Random(M);
  catch err
    error "Base ring has no random algorithm.";
  end try;
  t := T!Eltseq(m @ T`UniMap);
  t`Element := m;
  return t;
end intrinsic;

intrinsic RandomTensor( R::Rng, S::[RngIntElt], Cat::TenCat ) -> TenSpcElt
{Returns a random tensor of the finite R-tensor space with the given dimensions and category.}
  require __HasRandom(R) : "Base ring has no random algorithm.";
  if Cat`Contra then
    require ISA(Type(R),Fld) : "Base ring must be a field for cotensors.";
    return Random(KCotensorSpace(R,S,Cat));
  end if;
  return Random(RTensorSpace(R,S,Cat));
end intrinsic;

intrinsic RandomTensor( R::Rng, S::[RngIntElt] ) -> TenSpcElt
{Returns a random tensor of the finite R-tensor space with the given dimensions.}
  require __HasRandom(R) : "Base ring has no random algorithm.";
  return Random(RTensorSpace(R,S));
end intrinsic;

intrinsic RandomCotensor( K::Fld, S::[RngIntElt] ) -> TenSpcElt
{Returns a random cotensor of the finite K-tensor space with the given dimensions.}
  require __HasRandom(K) : "Base ring has no random algorithm.";
  return Random(KCotensorSpace(K,S));
end intrinsic;

