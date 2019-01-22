
intrinsic AsFrame(modules::SeqEnum[MyMod]) -> TenFrm
{ The modules to form the frame. }
  F := New(TenFrm);
  F`Valence := #modules;
  //try // no error can happen as I typed the input more strongly.
    require forall{ M : M in modules | BaseRing(M) cmpeq BaseRing(modules[1]) } :
      "All modules must have a common base ring.";
  //catch err
  //  error "Entries in frame must have a module structure.";
  //end try;

  F`BaseRing := BaseRing(modules[1]);
  F`Modules := modules;
  return F;
end intrinsic;

intrinsic Eltseq(F::TenFrm) -> SeqEnum[MyMod]
{ The modules of the frame. }
    return F`Modules;
end intrinsic;

intrinsic '#'(F::TenFrm) -> RngIntElt
{ The valence of the frame. }
    return F`Valence;
end intrinsic;

intrinsic '.'(F::TenFrm, a::RngIntElt) -> MyMod
{ Return the a-th term in the frame. }
    return [F`Modules[#F-a+1]];
end intrinsic;
