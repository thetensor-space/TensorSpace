/* 
    Copyright 2016, 2017, Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


/*
  This file contains categorical functions for tensors (TenSpcElt).
*/


import "../GlobalVars.m" : __LIST, __SANITY_CHECK, __FRAME;
import "Tensor.m" : __GetTensor, __TensorOnVectorSpaces;
import "../Homotopisms/Hom.m" : __GetHomotopism;
import "../TensorCategory/TensorCat.m" : __TensorCatSanity;

__GetCoercedElt := function( t, x, i )
  try
    y := (__FRAME(t)[t`Valence-i])!x;
  catch err
    try
      y := (Domain(t`Coerce[t`Valence-i])!x) @ t`Coerce[t`Valence-i];
    catch err
      return false;
    end try;
  end try;
  return y;
end function;

__GetSpace := function( t, C, i )
  if Type(C) in {SeqEnum, SetEnum, List, SetIndx} then
    bas := [];
    for j in [1..#C] do
      c := __GetCoercedElt(t, C[j], i);
      if Type(c) ne BoolElt then
        Append(~bas, c);
      else 
        return false;
      end if;
    end for;
    S := sub< __FRAME(t)[t`Valence-i] | bas >;
  else 
    try
      return $$(t, Basis(C), i);
    catch err
      return $$(t, [C], i);
    end try;
  end if;
  return S;
end function;

__GenerateFrame := function( t, F )
  list := [**];
  for i in [1..#F] do
    X := __GetSpace(t, F[i], t`Valence-i);
    if Type(X) ne BoolElt then
      Append(~list, X); 
    else
      return false;
    end if;
  end for;
  return list;
end function;


// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
// Only implemented for homotopism category.
// ------------------------------------------------------------------------------
//                                     Submaps
// ------------------------------------------------------------------------------
intrinsic Subtensor( t::TenSpcElt, D::List, C::. ) -> TenSpcElt
{Returns the smallest submap of t containing the Cartesian product of D in the domain and C in the codomain.}
  require #D eq #t`Domain : "List does not correspond to domain.";
  if exists{ X : X in Frame(t) | Type(X) notin __LIST } then
    passed, t, _, err := __TensorOnVectorSpaces(t);
    require passed : err;
  end if;
  frame := __GenerateFrame(t, D cat [*C*]);
  require Type(frame) ne BoolElt : "Cannot coerce into frame.";
  Dom := frame[1..#frame-1];
  Dom := [* sub< X | Basis(X) > : X in Dom *]; // remove superfluous gens

  // Fill the image
  gens := CartesianProduct( < Basis(Dom[i]) : i in [1..#t`Domain] > );
  Cod := sub< t`Codomain | frame[#frame], { g @ t : g in gens } >;
  Cod := sub< Cod | Basis(Cod) >; // remove superfluous gens

  F := function(x)
    return < (t`Domain)[i]!(x[i]) : i in [1..#t`Domain] > @ t;
  end function;

  if assigned t`Coerce then
    Coerce := t`Coerce;
  else
    Coerce := false;
  end if;
  s := __GetTensor( Dom, Cod, F : Cat := t`Cat, Co := Coerce );
  passed, s, maps, err := __TensorOnVectorSpaces( s );
  require passed : err;
  return s;
end intrinsic;

intrinsic Subtensor( t::TenSpcElt, D::SeqEnum, C::. ) -> TenSpcElt
{Returns the smallest submap of t containing the Cartesian product of D in the domain and C in the codomain.}
  return Subtensor(t, [*X : X in D*], C);
end intrinsic;

intrinsic Subtensor( t::TenSpcElt, S::List ) -> TenSpcElt
{Returns the smallest submap of t containing S. 
The first v entries of S are contained in the domain of t, and the last entry of S is contained in the codomain of t.}
  require #S eq t`Valence : "List does not correspond to the frame.";
  return Subtensor( t, S[1..t`Valence-1], S[t`Valence] );
end intrinsic; 

intrinsic Subtensor( t::TenSpcElt, S::SeqEnum ) -> TenSpcElt
{Returns the smallest submap of t containing S. 
The first v entries of S are contained in the domain of t, and the last entry of S is contained in the codomain of t.}
  require #S eq t`Valence : "Sequence does not correspond to the frame.";
  return Subtensor( t, [*S[i] : i in [1..t`Valence-1]*], S[t`Valence] );
end intrinsic;

intrinsic IsSubtensor( t::TenSpcElt, s::TenSpcElt ) -> BoolElt
{Decides if s is a subtensor of t.}
  require t`Cat eq s`Cat : "Tensors not in the same category.";
  if exists{ X : X in Frame(t) | Type(X) notin __LIST } then
    passed, t, H2, err := __TensorOnVectorSpaces(t);
    require passed : err;
  end if;
  if exists{ X : X in Frame(s) | Type(X) notin __LIST } then
    passed, s, _, err := __TensorOnVectorSpaces(s);
    require passed : err;
  end if;

  d := forall{ i : i in [1..#s`Domain] | forall{ b : b in Basis(s`Domain[i]) | IsCoercible(t`Domain[i],b) } };
  if d then
    c := forall{ b : b in Basis(s`Codomain) | IsCoercible(t`Codomain,b) };
  else
    return false;
  end if;
  return c;
end intrinsic;

// ------------------------------------------------------------------------------
//                                     Ideals
// ------------------------------------------------------------------------------
intrinsic LocalIdeal( t::TenSpcElt, D::List, C::., A::{RngIntElt} ) -> TenSpcElt
{Returns the smallest submap of t which is a local ideal containing D in the domain and C in the codomain. 
Here, A is a subset of integers corresponding to the Cartesian factors in the domain.}
  require Arrows(t`Cat) eq [ 1 : i in [1..t`Valence] ] : "Ideal not implemented for this category.";
  require #D eq #t`Domain : "Argument 2 does not match the valence of argument 1.";
  require forall{ X : X in Frame(t) | Type(X) in __LIST } : "Domain and codomain must be vector spaces.";
  require A subset {1..#t`Domain} : "Argument 4 contains unknown values.";
  I := {@ t`Valence-s : s in A @};
  // Get the domain and codomain down to standard objects. 
  // Also, check that they lie in the correct spaces.  
  frame := __GenerateFrame(t, D cat [*C*]);
  require Type(frame) ne BoolElt : "Cannot coerce into frame.";
  Dom := frame[1..#frame-1];
  Cod := frame[#frame];

  // Fill the image.
  Im := {};
  for s in I do
    temp := [* X : X in Dom *];
    temp[s] := t`Domain[s];
    gens := CartesianProduct( < Basis( temp[i] ) : i in [1..#t`Domain] > );
    Im join:= { g : g in gens };
  end for;
  Cod := sub< t`Codomain | Cod, { g @ t : g in Im } >;
  Dom := [* sub< X | Basis(X) > : X in Dom *]; // reduce superfluous gens
  Cod := sub< Cod | Basis(Cod) >; // reduce superfluous gens
  
  F := function(x)
    return < (t`Domain)[i]!(x[i]) : i in [1..#t`Domain] > @ t;
  end function;

  if assigned t`Coerce then
    Coerce := t`Coerce;
  else
    Coerce := false;
  end if;
  s := __GetTensor( Dom, Cod, F : Cat := t`Cat, Co := Coerce );
  return s;
end intrinsic;

intrinsic LocalIdeal( t::TenSpcElt, D::SeqEnum, C::., A::{RngIntElt} ) -> TenSpcElt
{Returns the smallest submap of t which is a local ideal containing D in the domain and C in the codomain. 
Here, A is a subset of integers corresponding to the Cartesian factors in the domain.}
  return LocalIdeal(t, [*X : X in D*], C, A);
end intrinsic;

intrinsic LocalIdeal( t::TenSpcElt, S::List, A::{RngIntElt} ) -> TenSpcElt
{Returns the smallest submap of t which is a local ideal containing S. 
Here, A is a subset of integers corresponding to the Cartesian factors in the domain.}
  return LocalIdeal(t, S[1..t`Valence-1], S[t`Valence], A);
end intrinsic;

intrinsic LocalIdeal( t::TenSpcElt, S::SeqEnum, A::{RngIntElt} ) -> TenSpcElt
{Returns the smallest submap of t which is a local ideal containing S. 
Here, A is a subset of integers corresponding to the Cartesian factors in the domain.}
  return LocalIdeal(t, [*S[i] : i in [1..t`Valence-1]*], S[t`Valence], A);
end intrinsic;

intrinsic LocalIdeal( t::TenSpcElt, s::TenSpcElt, A::{RngIntElt} ) -> TenSpcElt
{Returns the smallest submap of t which is a local ideal containing s. 
Here, A is a subset of integers corresponding to the Cartesian factors in the domain.}
  return LocalIdeal(t, [* X : X in s`Domain *], s`Codomain, A);
end intrinsic;

intrinsic IsLocalIdeal( t::TenSpcElt, s::TenSpcElt, A::{RngIntElt} ) -> BoolElt
{Decide if s is a local ideal of t. 
Here, A is a subset of integers corresponding to the Cartesian factors in the domain.}
  require t`Cat eq s`Cat : "Tensors not in the same category.";
  require Arrows(t`Cat) eq [ 1 : i in [1..t`Valence] ] : "Ideals not implemented for this category.";
  require forall{ X : X in Frame(t) | Type(X) in __LIST } : "Domain and codomain of tensors must be vector spaces.";
  require forall{ X : X in Frame(s) | Type(X) in __LIST } : "Domain and codomain of tensors must be vector spaces.";
  n := #t`Domain;
  require A subset {1..n} : "Argument 3 contains unknown values.";
  S := {@ n-s+1 : s in A @};

  if not IsSubtensor(t,s) then
    return false;
  end if;

  // Check the definition.
  for k in S do
    temp := [* X : X in s`Domain *];
    temp[k] := t`Domain[k];
    gens := CartesianProduct( < Basis( temp[i] ) : i in [1..n] > );
    if exists{ g : g in gens | g @ t notin s`Codomain } then
      return false;
    end if;
  end for;
  return true;
end intrinsic;

intrinsic Ideal( t::TenSpcElt, D::List, C::. ) -> TenSpcElt
{Returns the smallest submap of t containing D in the domain and C in the codomain that is an ideal of t.}
  return LocalIdeal(t, D, C, {1..#t`Domain});
end intrinsic;

intrinsic Ideal( t::TenSpcElt, D::SeqEnum, C::. ) -> TenSpcElt
{Returns the smallest submap of t containing D in the domain and C in the codomain that is an ideal of t.}
  return LocalIdeal(t, [*X : X in D*], C, {1..#t`Domain});
end intrinsic;

intrinsic Ideal( t::TenSpcElt, S::List ) -> TenSpcElt
{Returns the smallest submap of t containing S that is an ideal of t.}
  return LocalIdeal(t, S[1..t`Valence-1], S[t`Valence], {1..#t`Domain});
end intrinsic;

intrinsic Ideal( t::TenSpcElt, S::SeqEnum ) -> TenSpcElt
{Returns the smallest submap of t containing S that is an ideal of t.}
  return LocalIdeal(t, [*S[i] : i in [1..t`Valence-1]*], S[t`Valence], {1..#t`Domain});
end intrinsic;

intrinsic Ideal( t::TenSpcElt, s::TenSpcElt ) -> TenSpcElt
{Returns the smallest submap of t containing s that is an ideal of t.}
  require t`Valence eq s`Valence : "Valences do not match.";
  return LocalIdeal(t, [* x : x in s`Domain *], s`Codomain, {1..#t`Domain});
end intrinsic;

intrinsic IsIdeal( t::TenSpcElt, s::TenSpcElt ) -> BoolElt
{Decides if s is an ideal of t.}
  return IsLocalIdeal(t, s, {1..#s`Domain});
end intrinsic;

// ------------------------------------------------------------------------------
//                                    Quotients
// ------------------------------------------------------------------------------
intrinsic LocalQuotient( t::TenSpcElt, s::TenSpcElt, A::{RngIntElt} : Check := true ) -> TenSpcElt, Hmtp
{Returns the local quotient of t by the local ideal s. 
Here, A is a subset of integers corresponding to the Cartesian factors in the domain.}
  require t`Cat eq s`Cat : "Tensors not in the same category.";
  require Arrows(t`Cat) eq [ 1 : i in [1..t`Valence] ] : "Quotient not implemented for this category.";
  if exists{ X : X in Frame(t) | Type(X) notin __LIST } then
    passed, t, H2, err := __TensorOnVectorSpaces(t);
    require passed : err;
  end if;
  if exists{ X : X in Frame(s) | Type(X) notin __LIST } then
    passed, s, _, err := __TensorOnVectorSpaces(s);
    require passed : err;
  end if;
  n := #t`Domain;
  require A subset {1..n} : "Argument 3 contains unknown values.";
  
  // Check S-ideal properties.
  if Check then
    require IsLocalIdeal( t, s, A ) : "Argument is not a local ideal.";
  end if;
  S := {@ n-s+1 : s in A @};

  D := [* *];
  projs := [* *];
  for i in [1..n] do
    if i in S then
      Q,pi := t`Domain[i] / s`Domain[i];
    else
      Q := t`Domain[i];
      pi := hom< Q -> Q | [ <x,x> : x in Basis( Q ) ] >;
    end if;
    Append( ~D, Q );
    Append( ~projs, pi );
  end for;
  C, pi := t`Codomain / s`Codomain;
  Append( ~projs, pi );

  F := function(x)
    return < x[i] @@ projs[i] : i in [1..n] > @ t @ pi;
  end function;

  Q := __GetTensor( D, C, F : Cat := t`Cat );
  H := __GetHomotopism( HomotopismCategory(t`Valence : Contravariant := t`Cat`Contra), projs : Cod := Q, Dom := t );
  if assigned H2 then
    H := H2*H;
  end if;
  return Q, H;
end intrinsic;

intrinsic Quotient( t::TenSpcElt, s::TenSpcElt : Check := true ) -> TenSpcElt, Hmtp
{Returns the quotient of t by the ideal s.}
  require t`Cat eq s`Cat : "Tensors not in the same category.";
  require Arrows(t`Cat) eq [ 1 : i in [1..t`Valence] ] : "Quotient not implemented for this category.";
  if Check then
    require IsIdeal( t, s ) : "Arugment is not an ideal.";
  end if;
  return LocalQuotient( t, s, {1..#t`Domain} : Check := false );
end intrinsic;

intrinsic '/'( t::TenSpcElt, s::TenSpcElt ) -> TenSpcElt, Hmtp
{Returns the quotient t/s.}
  return Quotient(t,s);
end intrinsic;
