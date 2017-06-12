/* 
    Copyright 2016, 2017, Joshua Maglione, James B. Wilson.
    Distributed under GNU GPLv3.
*/


/*
  This file contains all the low-level definitions for tensors (TenSpcElt).
*/


import "Tensor.m" : __GetTensor;
import "TensorBasic.m" : __HasBasis;

// given a vector, a tensor, and a coordinate (in [1..v-1]),
// returns 3 things: can be coerced into V_(v-1), the coreced elt, error message.
__CoerceIntoDomain := function( x, t, i )
  if IsCoercible(t`Domain[i], x) then // easy case
    return true, (t`Domain[i])!x, _;
  else
    if assigned t`Coerce and IsCoercible(Domain(t`Coerce[i]), x) then
      return true, (Domain(t`Coerce[i])!x) @ t`Coerce[i], _;
    else
      return false, _, "Cannot coerce coordinate: " cat IntegerToString(t`Valence-i) cat ".";
    end if;
  end if;
end function;

// ------------------------------------------------------------------------------
//                                      Print
// ------------------------------------------------------------------------------
intrinsic Print( t::TenSpcElt )
{Print t}
  D := t`Domain;
  if t`Cat`Contra then
    s := Sprintf( "Cotensor of valence %o, ", t`Valence );
    i := t`Valence-1;
    while i gt 1 do
      s cat:= Sprintf( "U%o x ", i);
      i -:= 1;
    end while;
    s cat:= Sprintf( "U1 >-> K" );
    i := t`Valence-1;
    for X in D do
      s cat:= Sprintf( "\nU%o : %o", i, X );
      i -:= 1;
    end for;
    printf s;
  else
    s := Sprintf( "Tensor of valence %o, ", t`Valence );
    i := t`Valence-1;
    while i gt 1 do
      s cat:= Sprintf( "U%o x ", i);
      i -:= 1;
    end while;
    s cat:= Sprintf( "U1 >-> U0" );
    i := t`Valence-1;
    for X in D do
      s cat:= Sprintf( "\nU%o : %o", i, X );
      i -:= 1;
    end for;
    printf s cat "\nU0 : %o", t`Codomain;
  end if;
end intrinsic;

// ------------------------------------------------------------------------------
//                                    Compare
// ------------------------------------------------------------------------------
intrinsic 'eq'( t::TenSpcElt, s::TenSpcElt ) -> BoolElt
{t eq s}
  if (t`Cat eq s`Cat) and (BaseRing(t) cmpeq BaseRing(s)) and (t`Domain cmpeq s`Domain) then
    try 
      _ := StructureConstants(t);
      _ := StructureConstants(s);
    catch e
      return forall{ x : x in CartesianProduct( <Generators(X) : X in t`Domain > ) | (x @ t) eq (x @ s) };
    end try;
    return t`CoordImages eq s`CoordImages;
  end if;
  return false;
end intrinsic;

// ------------------------------------------------------------------------------
//                                   Evaluation
// ------------------------------------------------------------------------------
intrinsic '@'( x::Tup, t::TenSpcElt ) -> .
{x @ t}
  // first check if any of the entries are spaces. 
  spaces := [ __HasBasis(y) : y in x ];

  if &or(spaces) then // there exists a subspace
    y := <>;
    for i in [1..#x] do
      if spaces[i] then
        Append(~y, Basis(x[i]));
      else
        Append(~y, [x[i]]);
      end if;
    end for;
    CP := CartesianProduct(y);
    B := [];
    for y in CP do
      z := <>;
      for i in [1..#y] do
        passed, v, err := __CoerceIntoDomain(y[i], t, i); // a try & catch might be faster?
        require passed : err;
        Append(~z, v);
      end for;
      Append(~B, z @ t`Map);
    end for;
    S := sub< t`Codomain | B >;
    return S;
  else // only "vectors" in x
    y := <>;
    for i in [1..#x] do
      passed, v, err := __CoerceIntoDomain(x[i], t, i); // a try & catch might be faster?
      require passed : err;
      Append(~y, v);
    end for;
    return y @ t`Map;
  end if;
end intrinsic;

// ------------------------------------------------------------------------------
//                                   Composition
// ------------------------------------------------------------------------------
intrinsic '*'( t::TenSpcElt, f::Map ) -> TenSpcElt
{t * f} 
  require not t`Cat`Contra : "Tensor must be covariant.";
  F := function(x)
    return x @ t @ f;
  end function;
  return __GetTensor( t`Domain, Codomain(f), F );
end intrinsic;

// ------------------------------------------------------------------------------
//                                     Parent
// ------------------------------------------------------------------------------
intrinsic Parent( t::TenSpcElt ) -> TenSpc
{Returns the parent of t.}
  if assigned t`Parent then
    return t`Parent;
  end if;
  require Type(BaseRing(t)) ne BoolElt : "Tensor has no base ring.";
  try
    if t`Cat`Contra then
      P := CotensorSpace( [* Generic(X) : X in Frame(t) *], t`Cat );
    else
      P := TensorSpace( [* Generic(X) : X in Frame(t) *], t`Cat );
    end if;
  catch err
    try 
      if t`Cat`Contra then
        P := CotensorSpace( [* Parent(X) : X in Frame(t) *], t`Cat );
      else
        P := TensorSpace( [* Parent(X) : X in Frame(t) *], t`Cat );
      end if;
    catch err
      if t`Cat`Contra then
        K := BaseRing(t);
        require ISA(Type(K),Fld) : "Base ring of cotensor must be a field.";
        P := KCotensorSpace( K, [ Dimension(X) : X in Frame(t) ], t`Cat ); 
      else
        P := RTensorSpace( BaseRing(t), [ Dimension(X) : X in Frame(t) ], t`Cat ); 
      end if;
    end try;
  end try;
  t`Parent := P;
  return P;
end intrinsic;

// ------------------------------------------------------------------------------
//                                Module Operations
// ------------------------------------------------------------------------------
intrinsic '+'( t::TenSpcElt, s::TenSpcElt ) -> TenSpcElt
{t+s}
  require Parent(t) eq Parent(s) : "Arguments are not compatible.";
  if (assigned t`Coerce) and (assigned s`Coerce) and (t`Coerce cmpeq s`Coerce) then
    coerce := t`Coerce;
  else
    coerce := false;
  end if;
  Mt := t`Map;
  Ms := s`Map;
  F := function(x)
    return (x@Mt) + (x@Ms);
  end function;
  return __GetTensor( Domain(t), Codomain(t), F : Par := Parent(t), Co := coerce, Cat := t`Cat );
end intrinsic;

intrinsic '-'( t::TenSpcElt, s::TenSpcElt ) -> TenSpcElt
{t-s}
  require Parent(t) eq Parent(s) : "Arguments are not compatible.";
  if (assigned t`Coerce) and (assigned s`Coerce) and (t`Coerce cmpeq s`Coerce) then
    coerce := t`Coerce;
  else
    coerce := false;
  end if;
  Mt := t`Map;
  Ms := s`Map;
  F := function(x)
    return (x@Mt) - (x@Ms);
  end function;
  return __GetTensor( Domain(t), Codomain(t), F : Par := Parent(t), Co := coerce, Cat := t`Cat );
end intrinsic;

intrinsic '-'( t::TenSpcElt ) -> TenSpcElt
{-t}
  return -1*t;
end intrinsic;

// This intrinsic is already in Magma, so we need to overwrite it. Ideally, we would delete it.
// However, not including it in this package leaves the default one in Magma.
intrinsic '*'( x::RngElt, B::TenSpcElt ) -> TenSpcElt
{k*t}
  // if x is a scalar, then scale the tensor
  if IsCoercible(BaseRing(B), x) then
    M := B`Map;
    F := function(y)
      return (BaseRing(B)!x)*(y @ M);
    end function;
    coerce := (assigned B`Coerce) select B`Coerce else false;
    parent := (assigned B`Parent) select B`Parent else false;
    return __GetTensor( B`Domain, B`Codomain, F : Par := parent, Co := coerce, Cat := B`Cat );
  end if;

  // at this point, x is not an obvious scalar.
  require B`Valence le 3 : "Arguments not compatible.";
  if B`Valence eq 2 then
    try
      return <x> @ B;
    catch err
      error "Argument not contained in the domain.";
    end try;
  end if;
  try
    x := B`Domain[1]!x;
  catch err
    try
      x := (Domain(B`Coerce[1])!x) @ B`Coerce[1];
    catch err
      error "Argument not contained in left domain.";
    end try;
  end try;
  V := B`Domain[2];
  W := B`Codomain;
  F := function(y)
    return < x,y[1] > @ B;
  end function;
  L := Tensor( [* V, W *], F );
  if assigned B`Coerce then
    L`Coerce := B`Coerce[2..3];
  end if;
  return L;
end intrinsic;
