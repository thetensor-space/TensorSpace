
intrinsic AsFrame(mods::SeqEnum) -> TenFrm
{ The modules to form the frame. }
  F := New(TenFrm);
  F`Valence := #mods;
  try
    require forall{ M : M in S | BaseRing(M) cmpeq BaseRing(S[1]) } :
      "All modules must have a common base ring.";
  catch err
    error "Entries in frame must have a module structure.";
  end try;

  F`BaseRing := BaseRing(S[1]);
  F`Modules := mods;
  return F;
end intrinsic;

intrinsic Eltseq(F::TenFrm) -> SeqEnum
    return F`Modules;
end intrinsic;

intrinsic '#'(F:TenFrm) -> RngIntElt
    return F`Valence;
end intrinsic;

intrinsic '.'(F::TenFrm, a::RngIntElt) -> ModRng 
{ Return the a-th term in the frame. }
    return F`Modules[#F-a+1];
end intrinsic;
