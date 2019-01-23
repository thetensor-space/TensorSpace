

// -----------------------------------------------------------------------------
//                                  Tensor Space
// TenSpc
// case UnitTenSpc <: TenSpc
//   
// case PolyTenSpc <: TenSpc
//   Frame::SeqEnum[UnitTenSpc]
// -----------------------------------------------------------------------------
declare type TenSpc[TenSpcElt]; // eventually inherit ModRng structure
declare attributes TenSpc : 
    Cat;                // Cat::TenCat . . . . . . The category of the tensor space tensors.
    // removed Ring, fetch from Frame or module.
    // removed Valence, fetch from Cat.

// ----------------------------------------------------------------------------
declare type UnitCoTenSpc : TenSpc;
declare attributes UnitTenSpc : 
    Coerce,             // Coerce . . . . . . . . If the space is created from some algebraic object, 
                                                    this will contain maps to the module.
    Mod,                // Mod::UnitTenSpc. . . . The f.g. R-module T.
    UniMap;             // UniMap . . . . . . . . A universal cotensor map: R^n -> M

declare type CoordMod;
declare attributes CoordMod :
    free,
    pi,
    sift;
    
/* 
    Create a  pi:R^n -> M and iota:M->R^n where m @ iota @ pi = m.
 */
__GetTensorSpaceOverVectorSpaces := function( R, M )
  FM := RSpace(R, Rank(M)); 
  pi := map< FM-> M | y :-> M!Coordinates(FM, y) >;
  sift := map< M -> FM | x :-> FM!Coordinates(M, x) >;
  return FM, pi, sift;
end function;


__UnitTensorSpace := function( mod )
    uts := New(UnitTenSpc);
    uts`Cat := 
    uts`Coerce := IsCoercable(mod);
    uts`Frame := New(SingletonTenFrm);
        uts`Frame`BaseRing := uts`Ring;
        uts`Frame`Modules := [mod];

    uts`Mod := mod;
    uts`Ring := BaseRing(mod);
    uts`UniMap = map< mod->mod : x :-> x>;
    return uts;
end function;


declare type PolyTenSpc : TenSpc;
declare attributes PolyTenSpc : Frame;

