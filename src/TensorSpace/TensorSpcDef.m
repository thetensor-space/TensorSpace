/* 
    Copyright 2016, 2017, Joshua Maglione, James B. Wilson.
    Distributed under GNU GPLv3.
*/


/*
  This file contains all the low-level definitions of tensor spaces (TenSpc).
*/


import "../GlobalVars.m" : __FRAME;

// ------------------------------------------------------------------------------
//                                      Print
// ------------------------------------------------------------------------------
intrinsic Print( T::TenSpc )
{Print T.}
  M := T`Frame;
  d := Dimension(T`Mod);
  if ISA(Type(T`Ring),FldFin) then
    if IsPrimeField(T`Ring) then
      ring := Sprintf( "GF(%o)", Characteristic(T`Ring) );
    else
      ring := Sprintf( "GF(%o^%o)", Characteristic(T`Ring), Degree(T`Ring) );
    end if;
  else
    ring := T`Ring;
  end if;
  if T`Cat`Contra then
    s := Sprintf( "Cotensor space of dimension %o over %o with valence %o\n", d, ring, T`Valence );
    for i in [1..T`Valence-2] do 
      s cat:= Sprintf( "U%o : %o\n", T`Valence - i, M[i] );
    end for;
    printf s cat Sprintf( "U1 : %o", M[#M-1] );
  else
    s := Sprintf( "Tensor space of dimension %o over %o with valence %o\n", d, ring, Valence(T) );
    for i in [1..T`Valence-1] do
      s cat:= Sprintf( "U%o : %o\n", T`Valence - i, M[i] );
    end for;
    printf s cat Sprintf( "U0 : %o", M[#M] );
  end if;
end intrinsic;

// ------------------------------------------------------------------------------
//                                    Compare
// ------------------------------------------------------------------------------
intrinsic 'eq'( T::TenSpc, S::TenSpc ) -> BoolElt
{T eq S}
  // easiest to hardest check. Once it fails it aborts.
  // note that cmpeq is "stronger" than eq: will sometimes report false when true, but never true when false.
  return (T`Valence eq S`Valence) and (T`Cat eq S`Cat) and (T`Ring cmpeq S`Ring) and (T`Mod cmpeq S`Mod) and (T`Frame cmpeq S`Frame);
end intrinsic;

// ------------------------------------------------------------------------------
//                                     Coerce
// ------------------------------------------------------------------------------
intrinsic IsCoercible( T::TenSpc, t::TenSpcElt ) -> BoolElt
{Determines if t is coercible in T.}
  if Parent(t) eq T then // if already in
    return true,t;
  end if;
  if assigned t`Element and IsCoercible(T`Mod,t`Element) then // if it has a corresponding element which is in the module
    t`Element := (T`Mod)!(t`Element);
    t`Parent := T;
    return true,t;
  end if;
  try
    sc := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;
  D := [ Dimension(X) : X in Frame(T) ];
  R := T`Ring;

  if t`Cat ne T`Cat then // check categories
    return false,"Incompatible categories.";
  end if; 
  if [ Dimension(X) : X in Frame(t) ] ne D then // check frames
    return false,"Incompatible frames.";
  end if;
  if not IsCoercible(R,sc[1]) then // check rings
    return false,"Cannot coerce ring structures.";
  end if;

  if IsCoercible(Codomain(T`UniMap),sc) then
    e := (Codomain(T`UniMap)!sc) @@ T`UniMap;
    if e notin T`Mod then
      return false,"Tensor not contained in tensor space.";
    end if;
    s := Tensor(R,D,Eltseq(e@T`UniMap),T`Cat);
    s`Parent := T;
    s`Element := e;
   if exists{ i : i in [1..#__FRAME(s)] | not __FRAME(s)[i] cmpeq __FRAME(T)[i] } then // if it has a different frame, fix
      try
        M := [* map< __FRAME(T)[i] -> __FRAME(s)[i] | x :-> (__FRAME(s)[i])!Coordinates(__FRAME(T)[i],x) > : i in [1..#__FRAME(T)] *];
        s`Coerce := M;
        s`Domain := __FRAME(T)[1..#__FRAME(T)-1];
        s`Codomain := __FRAME(T)[#__FRAME(T)];
        return true,s;
      catch err
        return false,"Incompatible";
      end try;
    end if;
    return true,s;
  end if;
  return false,"Incompatible.";
end intrinsic;

intrinsic IsCoercible( T::TenSpc, S::[RngElt] ) -> BoolElt
{Determines if S is coercible in T.}
  D := [ Dimension(X) : X in Frame(T) ];
  R := T`Ring;

  if &*D ne #S then // check frames
    return false,"Incompatible frames.";
  end if;
  if #S eq 0 then // check if T is 0-dimensional
    s := Tensor(R,D,[],T`Cat);
    s`Parent := T;
    s`Element := T`Mod!0;
    return true,s;
  end if;
  if not IsCoercible(R,S[1]) then // check rings
    return false,"Cannot coerce ring structures.";
  end if;

  if IsCoercible(Codomain(T`UniMap),S) then
    e := (Codomain(T`UniMap)!S) @@ T`UniMap;
    if e notin T`Mod then
      return false,"Tensor not contained in tensor space.";
    end if;
    s := Tensor(R,D,Eltseq(e@T`UniMap),T`Cat);
    s`Parent := T;
    s`Element := e;
   if exists{ i : i in [1..#__FRAME(s)] | not __FRAME(s)[i] cmpeq __FRAME(T)[i] } then // if it has a different frame, fix
      try
        M := [* map< __FRAME(T)[i] -> __FRAME(s)[i] | x :-> (__FRAME(s)[i])!Coordinates(__FRAME(T)[i],x) > : i in [1..#__FRAME(T)] *];
        s`Coerce := M;
        s`Domain := __FRAME(T)[1..#__FRAME(T)-1];
        s`Codomain := __FRAME(T)[#__FRAME(T)];
        return true,s;
      catch err
        return false,"Incompatible";
      end try;
    end if;
    return true,s;
  end if;
  return false,"Incompatible.";
end intrinsic;

// Only used to do T!0 to get the trivial tensor.
intrinsic IsCoercible( T::TenSpc, t::RngIntElt ) -> BoolElt
{Determines if t is coercible in T.}
  if t eq 0 then
    return true,T!(Eltseq(Codomain(T`UniMap)!0));
  end if;
  return false,"Incompatible.";
end intrinsic;

// ------------------------------------------------------------------------------
//                                  Membership
// ------------------------------------------------------------------------------
intrinsic 'in'( t::TenSpcElt, T::TenSpc ) -> BoolElt
{Decides if t is contained in T.}
  if Parent(t) eq T then // if tensor came from T
    return true;
  end if;
  if Parent(t) subset T then // if tensor came from a subspace of T
    return true;
  end if;
  if not assigned t`Element then // if no associated element, use Eltseq
    try
      m := Eltseq(t);
    catch err;
      error "Cannot compute structure constants.";
    end try;
    t`Element := RSpace(BaseRing(t),#m)!m;
  end if;
  try 
    return t`Element in T`Mod;
  catch err
    error "Cannot find covering space.";
  end try;
end intrinsic;

intrinsic 'subset'( S::TenSpc, T::TenSpc ) -> BoolElt
{Decides if S is a subset of T.}
  if (Generic(T) eq Generic(S)) and (Degree(S`Mod) eq Degree(T`Mod)) then
    try 
      return S`Mod subset T`Mod;
    catch err
      error "Cannot find covering space.";
    end try;
  end if;
  error "Cannot find covering space.";
end intrinsic;
