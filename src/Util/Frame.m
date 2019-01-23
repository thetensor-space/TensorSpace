/* 
    Copyright 2016, 2017, Joshua Maglione, James B. Wilson.
    Distributed under MIT Liscence
*/


// -----------------------------------------------------------------------------
//                                  Frame Types
// -----------------------------------------------------------------------------
declare type TenFrm;  // Tree type container class of tensor spaces of valence 1. 
declare attributes TenFrm : 
  Ring; // Base ring common to all children.

declare type UnitTenFrm : TenFrm;
declare attributes PolyTenFrm : 
  Mod, // the module
  Pos; // the position in the list.

declare type PolyTenFrm : TenFrm;
declare attributes PolyTenFrm : 
  Frames; // The subframes.

// -----------------------------------------------------------------------------
//                                  Frame Constructors
// -----------------------------------------------------------------------------

/*
    Frames are the list of modules on which a tensor spaces is defined.
    Their members are are Tensor Spaces themselves, of valence 1, which
    we record as the type TenSpcNull.
 */

__UnitTensorSpace := function( mod )
    uts := New(UnitTenSpc);
    uts`Cat := 
    uts`Coerce := IsCoercable(mod);
    uts`Frame := New(SingletonTenFrm);
        uts`Frame`BaseRing := uts`Ring;
        uts`Frame`Modules := [mod];

    uts`Mod := mod;
    uts`Ring := BaseRing(mod);
    uts`UniMap;
    return uts;
end function;

/*
 __ISARModule = function(R, mod)
    // Has it a ring?
    try
        // Every Magma module has a "BaseRing".
        S := BaseRing(mod);
        if not (S cmpeq R) then 
            return false;
        end if;
    catch err
        return false;
    end try;

    // Has it a sum and scalar action?
    try               
        temp := mod.1 + mod.1;
        temp := R.1*mod.1;
    catch err
        if Rank(mod) eq 0 then
            return RSpace(R,0);
        end if;
    end try;
    return true;
end function;
*/

intrinsic AsFrame(modules::SeqEnum) -> TenFrm
{ The modules to form the frame. }
  F := New(TenFrm);

  // Since Magma has no common parent type for modules
  // cannot use the type checker to force all inputs 
  // to be modules.  
  // Runtime check that each term is a "module" over a common ring.
  try
    require forall{ M : M in modules | BaseRing(M) cmpeq BaseRing(modules[1]) } :
      "All modules must have a common base ring.";
  catch err
    error "Entries in frame must have a module structure.";
  end try;
  F`BaseRing := BaseRing(modules[1]);
  F`Frames := [<i,__UnitTensorSpace(modules[i])> : i in [1..#modules]];
  return F;
end intrinsic;

// -----------------------------------------------------------------------------
//                                  Frame Methods
// -----------------------------------------------------------------------------

intrinsic Eltseq(F::TenFrm) -> SeqEnum[UnitTenSpc]
{ The modules of the frame. }
    return F`Modules;
end intrinsic;

intrinsic '#'(F::TenFrm) -> RngIntElt
{ The valence of the frame. }
    return #(F`Modules);
end intrinsic;

intrinsic '.'(F::PolyTenFrm, a::RngIntElt) -> TenSpc
{ Return the a-th term in the frame. }
    return [F`Mods[#F-a+1]];
end intrinsic;

intrinsic BaseRing(F::PolyTenFrm) -> TenSpc
{ The base ring of the frame.} 
    return F`Ring;
end intrinsic;

