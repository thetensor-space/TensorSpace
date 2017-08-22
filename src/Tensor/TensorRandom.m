/* 
    Copyright 2016, 2017, Joshua Maglione, James B. Wilson.
    Distributed under GNU GPLv3.
*/


/*
  This file contains functions to construct random (co)tensors.
*/


import "../GlobalVars.m" : __FRAME;
import "TensorData.m" : __GetShuffle;


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

__GetSymmetricTensor := function(R, d, n, c : anti := 0)
  // dumb case
  if n eq 1 then return RandomTensor(R, [d, c]); end if;

  // matrix case
  if n le 2 then
    try
      Mats := [RandomMatrix(R, d, d) : i in [1..c]];  
    catch err
      error "Base ring has no random algorithm.";
    end try;
    if anti eq 0 and Characteristic(R) eq 2 then
      return Tensor([X + Transpose(X) + DiagonalMatrix([Random(R) : i in [1..d]]) : X in Mats], 2, 1, TensorCategory([1,1,1], {{0},{1..2}}));
    else
      return Tensor([X + (-1)^anti*Transpose(X) : X in Mats], 2, 1, TensorCategory([1,1,1], {{0},{1..2}}));
    end if;
  end if;

  // general case
  V := RSpace(R, c*d^n);
  try
    t := Random(V);
  catch err
    error "Base ring has no random algorithm.";
  end try;
  G := Sym(n);
  dims := [d : i in [1..n]] cat [c];
  for g in G do
    if g ne G!1 then
      s := V!__GetShuffle(Eltseq(t), dims, [0] cat Eltseq(g));
      k := (Sign(g))^anti;
      t +:= k*s;
    end if;
  end for;
  if anti eq 0 and Characteristic(R) eq 2 then
    s := V!0;
    rand := [Random(R) : i in [1..c*d]];
    offsets := [c*d^i : i in [0..n-1]] cat [1];
    for a in [1..d] do
      for b in [1..c] do
        index := b + (&+[offsets[i]*(a-1): i in [1..n]]);
        s[index] := rand[(a-1)*c+b];
      end for;
    end for;
    t +:= s;
  end if;
  return Tensor(R, dims, Eltseq(t), TensorCategory([1 : i in [1..n+1]], {{0},{1..n}}));
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

intrinsic RandomTensor( R::Rng, S::[RngIntElt], C::TenCat ) -> TenSpcElt
{Returns a random tensor of the finite R-tensor space with the given dimensions and category.}
  require __HasRandom(R) : "Base ring has no random algorithm.";
  if C`Contra then
    require ISA(Type(R),Fld) : "Base ring must be a field for cotensors.";
    return Random(KCotensorSpace(R,S,C));
  end if;
  return Random(RTensorSpace(R,S,C));
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

intrinsic RandomAlternatingTensor( R::Rng, d::RngIntElt, n::RngIntElt, c::RngIntElt ) -> TenSpcElt
{Returns a random antisymmetric tensor of the finite R-tensor space (R^d)^n >-> R^c.}
  return __GetSymmetricTensor(R, d, n, c : anti := 1);
end intrinsic;

intrinsic RandomAlternatingTensor( R::Rng, S::[RngIntElt] ) -> TenSpcElt
{Returns a random antisymmetric tensor of the finite R-tensor space with the given dimensions.}
  require #S gt 1 : "Tensor must have valence greater than 1.";
  require #Set(Prune(S)) eq 1 : "Ranks in the domain must be equal.";
  return __GetSymmetricTensor(R, S[1], #S-1, S[#S] : anti := 1);
end intrinsic;

intrinsic RandomAntisymmetricTensor( R::Rng, d::RngIntElt, n::RngIntElt, c::RngIntElt ) -> TenSpcElt
{Returns a random antisymmetric tensor of the finite R-tensor space (R^d)^n >-> R^c.}
  return __GetSymmetricTensor(R, d, n, c : anti := (Characteristic(R) ne 2) select 1 else 0);
end intrinsic;

intrinsic RandomAntisymmetricTensor( R::Rng, S::[RngIntElt] ) -> TenSpcElt
{Returns a random alternating tensor of the finite R-tensor space with the given dimensions.}
  require #S gt 1 : "Tensor must have valence greater than 1.";
  require #Set(Prune(S)) eq 1 : "Ranks in the domain must be equal.";
  return __GetSymmetricTensor(R, S[1], #S-1, S[#S] : anti := (Characteristic(R) ne 2) select 1 else 0);
end intrinsic;

intrinsic RandomSymmetricTensor( R::Rng, d::RngIntElt, n::RngIntElt, c::RngIntElt ) -> TenSpcElt
{Returns a random symmetric tensor of the finite R-tensor space (R^d)^n >-> R^c.}
  return __GetSymmetricTensor(R, d, n, c);
end intrinsic;

intrinsic RandomSymmetricTensor( R::Rng, S::[RngIntElt] ) -> TenSpcElt
{Returns a random symmetric tensor of the finite R-tensor space with the given dimensions.}
  require #S gt 1 : "Tensor must have valence greater than 1.";
  require #Set(Prune(S)) eq 1 : "Ranks in the domain must be equal.";
  return __GetSymmetricTensor(R, S[1], #S-1, S[#S]);
end intrinsic;
