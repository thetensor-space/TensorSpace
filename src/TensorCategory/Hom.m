/* 
    Copyright 2016, 2017, Joshua Maglione, James B. Wilson.
    Distributed under GNU GPLv3.
*/


/* 
  This file contains all the homotopism constructors.
*/

import "../GlobalVars.m" : __FRAME;

__VerifyHomotopism := function( B, C, H )
  Dom := Domain(B);
  v := #Dom+1;
  Bas := CartesianProduct(< Basis(d) : d in Dom >);
//  y := <>;
//  for x in Bas do
//    for i in [1..#x] do
//      if x[i] notin Domain(H.(v-i)) then
//        return false;
//      else
//        Append(~y, x[i] @ H.(v-i));
//      end if;
//    end for;
//    if (x @ B) notin Domain(H.0) then
//      return false;
//    else
//      try 
//    end if;
//  end for;
  try  
    pass := forall{ x : x in Bas | (< x[i] @ H.(v-i) : i in [1..#x] > @ C) eq ((x @ B) @ H.0) };
  catch err 
    pass := false;
  end try;
  return pass;
end function;

__GetHomotopism := function( B, C, M : Cat := 0, Check := true )
  H := New(Hmtp);
  F_B := __FRAME(B);
  F_C := __FRAME(C);
  // the @ operator does not work for AlgMatElt or GrpMatElt
  while exists(i){ i : i in [1..#M] | ISA(Type(M[i]), AlgMatElt) or ISA(Type(M[i]), GrpMatElt) } do
    M[i] := Hom(F_B[i], F_C[i])!(M[i]);
  end while;
  H`Maps := M;
  H`Domain := B;
  H`Codomain := C;
  if Type(Cat) eq TenCat then
    H`Cat := Cat;
  else
    H`Cat := B`Cat;
  end if;
  if Check then
    verified := __VerifyHomotopism(B, C, H);
  else
    verified := true;
  end if;
  return H, verified;
end function;

// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
intrinsic Homotopism( t::TenSpcElt, s::TenSpcElt, M::List : Check := true ) -> Hmtp
{Constructs the homotopisms from t to s given by the maps in M.}
  require #M eq t`Valence : "Incorrect number of maps.";
  require t`Cat eq s`Cat : "Tensor categories are incompatible.";
  H, isit := __GetHomotopism( t, s, M : Check := Check );
  require isit : "Maps do not induce a homotopism.";
  return H;
end intrinsic;

intrinsic Homotopism( t::TenSpcElt, s::TenSpcElt, M::SeqEnum : Check := true ) -> Hmtp
{Constructs the homotopisms from t to s given by the maps in M.}
  require #M eq t`Valence : "Incorrect number of maps.";
  require t`Cat eq s`Cat : "Tensor categories are incompatible.";
  H, isit := __GetHomotopism( t, s, [*f : f in M*] : Check := Check );
  require isit : "Maps do not induce a homotopism.";
  return H;
end intrinsic;

intrinsic Homotopism( t::TenSpcElt, s::TenSpcElt, M::List, C::TenCat : Check := true ) -> Hmtp
{Constructs the homotopisms from t to s given by the maps in M and the tensor category C.}
  require #M eq t`Valence : "Incorrect number of maps.";
  require #M eq C`Valence : "Valence does not match the valence of tensors.";
  require t`Cat eq s`Cat : "Tensor categories are incompatible.";
  H, isit := __GetHomotopism( t, s, M : Cat := C, Check := Check );
  return H;
end intrinsic;

intrinsic Homotopism( t::TenSpcElt, s::TenSpcElt, M::SeqEnum, C::TenCat : Check := true ) -> Hmtp
{Constructs the homotopisms from t to s given by the maps in M and the tensor category C.}
  require #M eq t`Valence : "Incorrect number of maps.";
  require #M eq C`Valence : "Valence does not match the valence of tensors.";
  require t`Cat eq s`Cat : "Tensor categories are incompatible.";
  H, isit := __GetHomotopism( t, s, [*f : f in M*] : Cat := C, Check := Check );
  return H;
end intrinsic;

intrinsic IsHomotopism( t::TenSpcElt, s::TenSpcElt, M::List ) -> BoolElt
{Decides if the given maps are a homotopism from t to s.}
  require #M eq t`Valence : "Incorrect number of maps.";
  require t`Cat eq s`Cat : "Tensor categories are incompatible.";
  H, isit := __GetHomotopism( t, s, M );
  if isit then
    return isit, H;
  end if;
  return false, _;
end intrinsic;

intrinsic IsHomotopism( t::TenSpcElt, s::TenSpcElt, M::SeqEnum ) -> BoolElt
{Decides if the given maps are a homotopism from t to s.}
  require #M eq t`Valence : "Incorrect number of maps.";
  require t`Cat eq s`Cat : "Tensor categories are incompatible.";
  H, isit := __GetHomotopism( t, s, [*f : f in M*] );
  if isit then
    return isit, H;
  end if;
  return false, _;
end intrinsic;
