/* 
    Copyright 2016, 2017, Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


/* 
  This file contains all the homotopism constructors.
*/

import "../GlobalVars.m" : __FRAME;

__VerifyHomotopism := function( B, C, H )
  Dom := Domain(B);
  v := #Dom+1;
  Bas := CartesianProduct(< Basis(d) : d in Dom >);

  // This needs to be fixed... -JM
  try  
    pass := forall{ x : x in Bas | (< x[i] @ H.(v-i) : i in [1..#x] > @ C) eq ((x @ B) @ H.0) };
  catch err 
    pass := false;
  end try;

  return pass;
end function;

__GetHomotopism := function( Cat, M : Check := false, Cod := 0, Dom := 0 )
  H := New(Hmtp);
  // the @ operator does not work for AlgMatElt or GrpMatElt
  //while exists(i){ i : i in [1..#M] | ISA(Type(M[i]), AlgMatElt) or ISA(Type(M[i]), GrpMatElt) } do
  //  M[i] := Hom(F_B[i], F_C[i])!(M[i]);
  //end while;
  H`Maps := M;
  if Type(Dom) ne RngIntElt then
    H`Domain := Dom;
  end if;
  if Type(Cod) ne RngIntElt then
    H`Codomain := Cod;
  end if;
  H`Cat := Cat;
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
  H, isit := __GetHomotopism(t`Cat, M : Check := Check, Cod := s, Dom := t);
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
end intrinsic;

// =============================================================================
//                                     Tests
// =============================================================================
intrinsic IsHomotopism( t::TenSpcElt, s::TenSpcElt, M::List ) -> BoolElt
{Decides if the given maps form a homotopism from t to s.}
  require #M eq t`Valence : "Incorrect number of maps.";
  require t`Cat eq s`Cat : "Tensor categories are incompatible.";
  H, isit := __GetHomotopism(t, s, M);
  if isit then
    return isit, H;
  end if;
  return false, _;
end intrinsic;

intrinsic IsHomotopism( t::TenSpcElt, s::TenSpcElt, M::SeqEnum ) -> BoolElt
{Decides if the given maps form a homotopism from t to s.}
  return IsHomotopism(t, s, [*X : X in M*]);
end intrinsic;

intrinsic IsHomotopism( t::TenSpcElt, s::TenSpcElt, M::List, C::TenCat ) -> BoolElt
{Decides if the given maps form a homotopism from t to s in the tensor category C.}
  require #M eq t`Valence : "Incorrect number of maps.";
  require t`Cat eq s`Cat : "Tensor categories are incompatible.";
  H, isit := __GetHomotopism(t, s, M : Cat := C);
  if isit then
    return isit, H;
  end if;
  return false, _;
end intrinsic;

intrinsic IsHomotopism( t::TenSpcElt, s::TenSpcElt, M::SeqEnum, C::TenCat ) -> BoolElt
{Decides if the given maps form a homotopism from t to s in the tensor category C.}
  return IsHomotopism(t, s, [*X : X in M*], C);
end intrinsic;
