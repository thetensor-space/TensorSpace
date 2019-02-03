/* 
    Copyright 2016--2019 Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


/* 
  This file contains all the homotopism constructors.
*/

import "../Util/Util.m" : __List, __Tuple;


// arrow is assumed to be in {-1, 1}. 
__InterpretArrows := function(arrow)
  if arrow eq -1 then
    return 2;
  end if;
  return 1;
end function;

// Input: t: Tup, H: Hmtp, k: RngIntElt (either -1 or 1).
// Returns: Tup.
// If k == 1, then acts by maps in H "pointing down;" otherwise "pointing up."
__ActOnTuple := function(t, H, k)
  v := #t + 1;
  s := __List(t);
  for i in [1..#t] do
    if (v-i) @ H`Cat`Arrows eq k then 
      s[i] := t[i] @ H.(v-i);
    end if;
  end for;
  return __Tuple(s);
end function;

__VerifyHomotopism := function( s, t, H )
  v := Valence(s);

  // Bring in only relevant spaces
  Spaces := <>;
  for i in [1..v-1] do
    dom := [*Domain(s)[i], Domain(t)[i]*];
    Append(~Spaces, dom[__InterpretArrows((v-i) @ H`Cat`Arrows)]);
  end for;

  // Get a structure basis for the tensor product of 'Spaces'
  B := CartesianProduct(<Basis(X) : X in Spaces>);

  // Run the test
  try
    if 0 @ H`Cat`Arrows eq 1 then
      pass := forall{x : x in B | __ActOnTuple(x, H, 1) @ t eq 
          (__ActOnTuple(x, H, -1) @ s) @ H.0};
    else
      pass := forall{x : x in B | (__ActOnTuple(x, H, 1) @ t) @ H.0 eq 
          __ActOnTuple(x, H, -1) @ s};
    end if;
  catch err
    "Something went wrong trying to apply one of the maps.";
    pass := false;
  end try;

  return pass;
end function;

__GetHomotopism := function( Cat, M : Check := false, Cod := 0, Dom := 0 )
  H := New(Hmtp);

  // the @ operator does not work for AlgMatElt or GrpMatElt
  while exists(i){ i : i in [1..#M] | ISA(Type(M[i]), AlgMatElt) or 
      ISA(Type(M[i]), GrpMatElt) } do
    K := BaseRing(M[i]);
    U := VectorSpace(K, Nrows(M[i]));
    V := VectorSpace(K, Ncols(M[i]));
    M[i] := Hom(U, V)!(M[i]);
  end while;

  H`Cat := Cat;
  H`Maps := M;
  if Type(Dom) ne RngIntElt then
    H`Domain := Dom;
  end if;
  if Type(Cod) ne RngIntElt then
    H`Codomain := Cod;
  end if;

  if Check then
    assert RngIntElt notin {Type(Dom), Type(Cod)};
    verified := __VerifyHomotopism(Dom, Cod, H);
  else
    verified := true;
  end if;

  return H, verified;
end function;

// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
// =============================================================================
//                                 Constructors
// =============================================================================
intrinsic Homotopism( t::TenSpcElt, s::TenSpcElt, M::List, C::TenCat : Check := true ) -> Hmtp
{Constructs the homotopism, in the tensor category C, from t to s given by the maps in M.}
  require #M eq t`Valence : "Number of maps and tensor valence do not match.";
  require #M eq C`Valence : "Number of maps and valence of given category do not match.";
  require t`Cat eq s`Cat : "Tensor categories are incompatible."; // Maybe we loosen this later?
  H, isit := __GetHomotopism(C, M : Check := Check, Cod := s, Dom := t);
  return H;
end intrinsic;

intrinsic Homotopism( t::TenSpcElt, s::TenSpcElt, M::SeqEnum, C::TenCat : Check := true ) -> Hmtp
{Constructs the homotopism, in the tensor category C, from t to s given by the maps in M.}
  return Homotopism(t, s, [*f : f in M*], C : Check := Check);
end intrinsic;

intrinsic Homotopism( t::TenSpcElt, s::TenSpcElt, M::List : Check := true ) -> Hmtp
{Constructs the homotopism from t to s given by the maps in M.}
  return Homotopism(t, s, M, t`Cat : Check := Check);
end intrinsic;

intrinsic Homotopism( t::TenSpcElt, s::TenSpcElt, M::SeqEnum : Check := true ) -> Hmtp
{Constructs the homotopism from t to s given by the maps in M.}
  return Homotopism(t, s, [*f : f in M*], t`Cat : Check := Check);
end intrinsic;

intrinsic Homotopism( M::List, C::TenCat ) -> Hmtp
{Constructs the homotopism, in the tensor category C, from the maps in M.}
  require #M eq C`Valence : "Number of maps do not match the valence of the tensor category.";
  H := __GetHomotopism(C, M : Check := false);
  return H;
end intrinsic;

intrinsic Homotopism( M::SeqEnum, C::TenCat ) -> Hmtp
{Constructs the homotopism, in the tensor category C, from the maps in M.}
  return Homotopism([*X : X in M*], C);
end intrinsic;

// =============================================================================
//                                     Tests
// =============================================================================
intrinsic IsHomotopism( t::TenSpcElt, s::TenSpcElt, M::List, C::TenCat ) -> BoolElt
{Decides if the given maps form a homotopism from t to s in the tensor category C.}
  require #M eq t`Valence : "Incorrect number of maps.";
  require t`Cat eq s`Cat : "Tensor categories are incompatible.";
  H, isit := __GetHomotopism(C, M : Check := true, Cod := s, Dom := t);
  if isit then
    return isit, H;
  end if;
  return false, _;
end intrinsic;

intrinsic IsHomotopism( t::TenSpcElt, s::TenSpcElt, M::SeqEnum, C::TenCat ) -> BoolElt
{Decides if the given maps form a homotopism from t to s in the tensor category C.}
  return IsHomotopism(t, s, [*X : X in M*], C);
end intrinsic;

intrinsic IsHomotopism( t::TenSpcElt, s::TenSpcElt, M::List ) -> BoolElt
{Decides if the given maps form a homotopism from t to s.}
  return IsHomotopism(t, s, M, HomotopismCategory(Valence(t)));
end intrinsic;

intrinsic IsHomotopism( t::TenSpcElt, s::TenSpcElt, M::SeqEnum ) -> BoolElt
{Decides if the given maps form a homotopism from t to s.}
  return IsHomotopism(t, s, [*X : X in M*], HomotopismCategory(Valence(t)));
end intrinsic;


