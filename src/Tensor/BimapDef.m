/* 
    Copyright 2016, 2017, Joshua Maglione, James B. Wilson.
    Distributed under GNU GPLv3.
*/



/*
  This file contains low-level definitions the bimap types: BmpU, BmpV, BmpUElt, 
  and BmpVElt.
*/

import "Tensor.m" : __GetTensor;
import "TensorDef.m" : __HasBasis;
import "../TensorCategory/TensorCat.m" : __GetTensorCategory;
import "../TensorSpace/TensorSpc.m" : __GetTensorSpace;

// meant for x*T or T*y
__GetTensorAction := function(x, T, i)
  // if x is a scalar, then scale the tensor.
  if IsCoercible(BaseRing(T), x) then
    M := T`Map;
    F := function(y)
      return (BaseRing(T)!x)*(y @ M);
    end function;
    coerce := (assigned T`Coerce) select T`Coerce else false;
    parent := (assigned T`Parent) select T`Parent else false;
    return __GetTensor( T`Domain, T`Codomain, F : Par := parent, Co := coerce, Cat := T`Cat );
  end if;

  // if T is a linear map, evaluate.
  if T`Valence eq 2 then
    try
      return <x> @ T;
    catch err
      error "Argument not contained in the domain.";
    end try;
  end if;

  // at this point, T is a 3-tensor.
  // first get the correct category.
  Cat := __GetTensorCategory(T`Cat`Arrows, T`Cat`Repeats : Con := T`Cat`Contra); 
  Cat`Valence -:= 1;
  j := (i eq 1) select 2 else 1;
  Cat`Arrows := map< {1,0} -> {-1,0,1} | <0, 0@T`Cat`Arrows>, <1, j@T`Cat`Arrows> >;
  assert exists(S){ S : S in Cat`Repeats | i in S };
  Exclude(~Cat`Repeats, S);
  if #S gt 1 then
    Include(~Cat`Repeats, Exclude(S, i));
  end if;
  assert exists(S){ S : S in Cat`Repeats | j in S };
  Exclude(~Cat`Repeats, S);
  Include(~Cat`Repeats, Include(Exclude(S, j), 1));

  // get underlying tensor space
  coerce := (assigned T`Coerce) select T`Coerce[Remove([1..3],j)] else false;
  parent := __GetTensorSpace(BaseRing(T), [*T`Domain[i], T`Codomain*], Cat : Co := coerce);

  if __HasBasis(x) then // if x is a subspace, return sub tensor space.
    S := sub< parent | <$$(b, T, i) : b in Basis(x)> >; // can't use SeqEnum... eventually fix.
    return S;
  else 
    try
      x := T`Domain[j]!x;
    catch err
      try
        x := (Domain(T`Coerce[j])!x) @ T`Coerce[j];
      catch err
        error "Argument not contained in right domain.";
      end try;
    end try;
    if i eq 1 then 
      F := function(y)
        return < y[1], x > @ T;
      end function;
    else
      F := function(y)
        return < x, y[1] > @ T;
      end function;
    end if;
    L := __GetTensor( [*T`Domain[i]*], T`Codomain, F : Co := coerce, Cat := Cat );
    return parent!L;
  end if;
end function;

// ------------------------------------------------------------------------------
//                                      Print
// ------------------------------------------------------------------------------
intrinsic Print( U::BmpU )
{Print U}
  printf "Bimap space U: %o", U`Space;
end intrinsic;

intrinsic Print( V::BmpV )
{Print V}
  printf "Bimap space V: %o", V`Space;
end intrinsic;

intrinsic Print( u::BmpUElt )
{Print u}
  printf "Bimap element of U: %o", u`Element;
end intrinsic;

intrinsic Print( v::BmpVElt )
{Print v}
  printf "Bimap element of V: %o", v`Element;
end intrinsic;

// ------------------------------------------------------------------------------
//                                     Coerce
// ------------------------------------------------------------------------------
// Need to check if Generators will return erorrs on x. 
// If it will return an error, this function returns false.
__IsSpace := function( x )
  try 
    gens := Generators(x);
  catch e
    if assigned e`Object then
      return false;
    end if;
  end try;
  return true;
end function;

intrinsic IsCoercible( U::BmpU, x::. ) -> BoolElt, BmpUElt
{Decides if x can be coerced into U, and if so, returns the result.}
  B := Parent(U);
  if assigned B`Coerce then // first check we have a coerce function
    if IsCoercible(Domain(B`Coerce[1]),x) then // is it an element?
      x := (Domain(B`Coerce[1])!x) @ B`Coerce[1];
    else
      if __IsSpace(x) and forall{ g : g in Generators(x) | IsCoercible(Domain(B`Coerce[1]),g) } then // is it a space?
        x := sub< Codomain(B`Coerce[1]) | [ (Domain(B`Coerce[1])!g) @ B`Coerce[1] : g in Generators(x) ] >;
      end if;
    end if;
  end if;
  if IsCoercible( U`Space, x ) then
    u := New(BmpUElt);
    u`Parent := U;
    u`Element := U`Space!x;
    return true, u;
  elif Type( U`Space ) eq Type( x ) and forall{ g : g in Generators(x) | IsCoercible( U`Space, g ) } then
    X := New(BmpU);
    X`Parent := B;
    X`Space := sub< U`Space | [ U`Space!g : g in Generators(x) ] >;
    return true, X;
  else
    return false,"Arguments are incompatible.";
  end if;
end intrinsic;

intrinsic IsCoercible( V::BmpV, x::. ) -> BoolElt, BmpVElt
{Decides if x can be coerced into V, and if so, returns the result.}
  B := Parent(V);
  if assigned B`Coerce then // first check we have a coerce function
    if IsCoercible(Domain(B`Coerce[2]),x) then // is it an element?
      x := (Domain(B`Coerce[2])!x) @ B`Coerce[2];
    else
      if __IsSpace(x) and forall{ g : g in Generators(x) | IsCoercible(Domain(B`Coerce[2]),g) } then // is it a space?
        x := sub< Codomain(B`Coerce[2]) | [ (Domain(B`Coerce[2])!g) @ B`Coerce[2] : g in Generators(x) ] >;
      end if;
    end if;
  end if;
  if IsCoercible( V`Space, x ) then
    v := New(BmpVElt);
    v`Parent := V;
    v`Element := V`Space!x;
    return true, v;
  elif Type( V`Space ) eq Type( x ) and forall{ g : g in Generators(x) | IsCoercible( V`Space, g ) } then
    X := New(BmpV);
    X`Parent := Parent(V);
    X`Space := sub< V`Space | [ V`Space!g : g in Generators(x) ] >;
    return true, X;
  else
    return false,"Arguments are incompatible.";
  end if;
end intrinsic;

// ------------------------------------------------------------------------------
//                                     Parent
// ------------------------------------------------------------------------------
intrinsic Parent( X::BmpU ) -> TenSpcElt
{Returns the parent bilinear map for X.}
  return X`Parent;
end intrinsic;

intrinsic Parent( X::BmpV ) -> TenSpcElt
{Returns the parent bilinear map for X.}
  return X`Parent;
end intrinsic;

intrinsic Parent( x::BmpUElt ) -> BmpU
{Returns the parent U for x.}
  return x`Parent;
end intrinsic;

intrinsic Parent( x::BmpVElt ) -> BmpV
{Returns the parent V for x.}
  return x`Parent;
end intrinsic;

intrinsic LeftDomain( t::TenSpcElt ) -> BmpU
{Returns the left domain of t used for coercion.}
  require t`Valence eq 3 : "Must be a valence 3 tensor.";
  return t`Bimap`U;
end intrinsic;

intrinsic RightDomain( t::TenSpcElt ) -> BmpV
{Returns the right domain of t used for coercion.}
  require t`Valence eq 3 : "Must be a valence 3 tensor.";
  return t`Bimap`V;
end intrinsic;

// ------------------------------------------------------------------------------
//                                     Compare
// ------------------------------------------------------------------------------
intrinsic 'eq'( u1::BmpUElt, u2::BmpUElt ) -> BoolElt
{Decides if u1 and u2 are the same.}
  return u1`Element eq u2`Element;
end intrinsic;

intrinsic 'eq'( v1::BmpVElt, v2::BmpVElt ) -> BoolElt
{Decides if v1 and v2 are the same.}
  return v1`Element eq v2`Element;
end intrinsic;

intrinsic 'eq'( U1::BmpU, U2::BmpU ) -> BoolElt
{Decides if U1 and U2 are the same.}
  return U1`Space eq U2`Space;
end intrinsic;

intrinsic 'eq'( V1::BmpV, V2::BmpV ) -> BoolElt
{Decides if V1 and V2 are the same.}
  return V1`Space eq V2`Space;
end intrinsic;

// ------------------------------------------------------------------------------
//                             Multiplication : x * y
// ------------------------------------------------------------------------------
// Elements
intrinsic '*'( x::BmpUElt, y::BmpVElt ) -> .
{x * y}
  require Parent(Parent(x)) eq Parent(Parent(y)) : "Elements come from different bimaps.";
  B := Parent(Parent(x));
  u := x`Element;
  v := y`Element;
  return <u,v> @ B`Map;
end intrinsic;

// Subspaces
intrinsic '*'( X::BmpU, Y::BmpV ) -> .
{X * Y}
  require Parent(X) eq Parent(Y) : "Subspaces come from different bimaps.";
  B := Parent(X);
  S := X`Space;
  T := Y`Space;
  Z := sub< B`Codomain | [ <x,y> @ B`Map : x in Generators(S), y in Generators(T) ] >;
  return Z;
end intrinsic;

// Mixed: elements and subspaces
intrinsic '*'( x::BmpUElt, Y::BmpV ) -> .
{x * Y}
  require Parent(Parent(x)) eq Parent(Y) : "Arguments come from different bimaps.";
  B := Parent(Y);
  u := x`Element;
  S := Y`Space;
  Z := sub< B`Codomain | [ <u,y> @ B`Map : y in Generators(S) ] >;
  return Z;
end intrinsic;

// Mixed: subspaces and elements
intrinsic '*'( X::BmpU, y::BmpVElt ) -> .
{X * Y}
  require Parent(X) eq Parent(Parent(y)) : "Arguments come from different bimaps.";
  B := Parent(X);
  S := X`Space;
  v := y`Element;
  Z := sub< B`Codomain | [ <x,v> @ B`Map : x in Generators(S) ] >;
  return Z;
end intrinsic;


// The following are possible user errors. The goal is to have all the possibilities defined,
// so that the error statement points to the problem instead of saying the product isn't defined.
//1
intrinsic '*'( x::BmpVElt, y::BmpUElt ) -> .
{x * y}
  require Parent(Parent(x)) eq Parent(Parent(y)) : "Elements come from different bimaps.";
  B := Parent(Parent(x));
  require IsCoercible( B`Bimap`U`Space, x`Element ) : "Argument 1 not in left domain.";
  x := B`Bimap`U`Space!(x`Element);
  require IsCoercible( B`Bimap`V`Space, y`Element ) : "Argument 2 not in right domain.";
  y := B`Bimap`V`Space!(y`Element);
  return (B`Bimap`U!x) * (B`Bimap`V!y);
end intrinsic;

//2
intrinsic '*'( X::BmpV, y::BmpUElt ) -> .
{X * y}
  require Parent(X) eq Parent(Parent(y)) : "Elements come from different bimaps.";
  B := Parent(X);
  require forall{ x : x in Generators(X`Space) | IsCoercible( B`Bimap`U`Space, x ) } : "Argument 1 not in left domain.";
  X := sub< B`Bimap`U`Space | [ B`Bimap`U`Space!x : x in Generators(X`Space) ] >;
  require IsCoercible( B`Bimap`V`Space, y`Element ) : "Argument 2 not in right domain.";
  y := B`Bimap`V`Space!(y`Element);
  return (B`Bimap`U!X) * (B`Bimap`V!y);
end intrinsic;

//3
intrinsic '*'( x::BmpVElt, Y::BmpU ) -> .
{x * Y}
  require Parent(Parent(x)) eq Parent(Y) : "Elements come from different bimaps.";
  B := Parent(Y);
  require IsCoercible( B`Bimap`U`Space, x`Element ) : "Argument 1 not in left domain.";
  x := B`Bimap`U`Space!(x`Element);
  require forall{ y : y in Generators(Y`Space) | IsCoercible( B`Bimap`V`Space, y ) } : "Argument 2 not in right domain.";
  Y := sub< B`Bimap`V`Space | [ B`Bimap`V`Space!y : y in Generators(Y`Space) ] >;
  return (B`Bimap`U!x) * (B`Bimap`V!Y);
end intrinsic;

//4
intrinsic '*'( X::BmpV, Y::BmpU ) -> .
{X * Y}
  require Parent(X) eq Parent(Y) : "Elements come from different bimaps.";
  B := Parent(X);
  require forall{ x : x in Generators(X`Space) | IsCoercible( B`Bimap`U`Space, x ) } : "Argument 1 not in left domain.";
  X := sub< B`Bimap`U`Space | [ B`Bimap`U`Space!x : x in Generators(X`Space) ] >;
  require forall{ y : y in Generators(Y`Space) | IsCoercible( B`Bimap`V`Space, y ) } : "Argument 2 not in right domain.";
  Y := sub< B`Bimap`V`Space | [ B`Bimap`V`Space!y : y in Generators(Y`Space) ] >;
  return (B`Bimap`U!X) * (B`Bimap`V!Y);
end intrinsic;

//5
intrinsic '*'( x::BmpUElt, y::BmpUElt ) -> .
{x * y}
  require Parent(Parent(x)) eq Parent(Parent(y)) : "Elements come from different bimaps.";
  B := Parent(Parent(x));
  require IsCoercible( B`Bimap`V`Space, y`Element ) : "Argument 2 not in right domain.";
  y := B`Bimap`V`Space!(y`Element);
  return x * (B`Bimap`V!y);
end intrinsic;

//6
intrinsic '*'( X::BmpU, y::BmpUElt ) -> .
{X * y}
  require Parent(X) eq Parent(Parent(y)) : "Elements come from different bimaps.";
  B := Parent(X);
  require IsCoercible( B`Bimap`V`Space, y`Element ) : "Argument 2 not in right domain.";
  y := B`Bimap`V`Space!(y`Element);
  return X * (B`Bimap`V!y);
end intrinsic;

//7
intrinsic '*'( x::BmpUElt, Y::BmpU ) -> .
{x * Y}
  require Parent(Parent(x)) eq Parent(Y) : "Elements come from different bimaps.";
  B := Parent(Y);
  require forall{ y : y in Generators(Y`Space) | IsCoercible( B`Bimap`V`Space, y ) } : "Argument 2 not in right domain.";
  Y := sub< B`Bimap`V`Space | [ B`Bimap`V`Space!y : y in Generators(Y`Space) ] >;
  return x * (B`Bimap`V!Y);
end intrinsic;

//8
intrinsic '*'( X::BmpU, Y::BmpU ) -> .
{X * Y}
  require Parent(X) eq Parent(Y) : "Elements come from different bimaps.";
  B := Parent(X);
  require forall{ y : y in Generators(Y`Space) | IsCoercible( B`Bimap`V`Space, y ) } : "Argument 2 not in right domain.";
  Y := sub< B`Bimap`V`Space | [ B`Bimap`V`Space!y : y in Generators(Y`Space) ] >;
  return X * (B`Bimap`V!Y);
end intrinsic;

//9
intrinsic '*'( x::BmpVElt, y::BmpVElt ) -> .
{x * y}
  require Parent(Parent(x)) eq Parent(Parent(y)) : "Elements come from different bimaps.";
  B := Parent(Parent(x));
  require IsCoercible( B`Bimap`U`Space, x`Element ) : "Argument 1 not in left domain.";
  x := B`Bimap`U`Space!(x`Element);
  return (B`Bimap`U!x) * y;
end intrinsic;

//10
intrinsic '*'( X::BmpV, y::BmpVElt ) -> .
{X * y}
  require Parent(X) eq Parent(Parent(y)) : "Elements come from different bimaps.";
  B := Parent(X);
  require forall{ x : x in Generators(X`Space) | IsCoercible( B`Bimap`U`Space, x ) } : "Argument 1 not in left domain.";
  X := sub< B`Bimap`U`Space | [ B`Bimap`U`Space!x : x in Generators(X`Space) ] >;
  return (B`Bimap`U!X) * y;
end intrinsic;

//11
intrinsic '*'( x::BmpVElt, Y::BmpV ) -> .
{x * Y}
  require Parent(Parent(x)) eq Parent(Y) : "Elements come from different bimaps.";
  B := Parent(Y);
  require IsCoercible( B`Bimap`U`Space, x`Element ) : "Argument 1 not in left domain.";
  x := B`Bimap`U`Space!(x`Element);
  return (B`Bimap`U!x) * Y;
end intrinsic;

//12
intrinsic '*'( X::BmpV, Y::BmpV ) -> .
{X * Y}
  require Parent(X) eq Parent(Y) : "Elements come from different bimaps.";
  B := Parent(X);
  require forall{ x : x in Generators(X`Space) | IsCoercible( B`Bimap`U`Space, x ) } : "Argument 1 not in left domain.";
  X := sub< B`Bimap`U`Space | [ B`Bimap`U`Space!x : x in Generators(X`Space) ] >;
  return (B`Bimap`U!X) * Y;
end intrinsic;

// ------------------------------------------------------------------------------
//                            Muliplication : x * t * y
// ------------------------------------------------------------------------------
intrinsic '*'( x::., t::TenSpcElt ) -> .
{x * t}
  require t`Valence le 3 : "Operation only defined for tensors of valence less than 4.";
  return __GetTensorAction(x, t, 2);
end intrinsic;

intrinsic '*'( t::TenSpcElt, y::. ) -> .
{t * y}
  require t`Valence le 3 : "Operation only defined for tensors of valence less than 4.";
  return __GetTensorAction(y, t, 1);
end intrinsic;
