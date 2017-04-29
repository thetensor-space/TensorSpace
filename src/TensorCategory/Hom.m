/* 
  This file contains all the homotopism constructors.
*/

__VerifyHomotopism := function( B, C, H )
  Dom := Domain(B);
  v := #Dom+1;
  Bas := CartesianProduct(< Basis(d) : d in Dom >);
  return forall{ x : x in Bas | (< x[i] @ H.(v-i) : i in [1..#x] > @ C) eq ((x @ B) @ H.0) };
end function;

__GetHomotopism := function( B, C, M : Cat := 0, Check := true )
  H := New(Hmtp);
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

intrinsic Homotopism( t::TenSpcElt, s::TenSpcElt, M::List, C::TenCat : Check := true ) -> Hmtp
{Constructs the homotopisms from t to s given by the maps in M and the tensor category C.}
  require #M eq t`Valence : "Incorrect number of maps.";
  require #M eq C`Valence : "Valence does not match the valence of tensors.";
  require t`Cat eq s`Cat : "Tensor categories are incompatible.";
  H, isit := __GetHomotopism( t, s, M : Cat := C, Check := Check );
  return H;
end intrinsic;
