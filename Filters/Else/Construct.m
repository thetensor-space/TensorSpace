intrinsic CheckCommutators( F::Flt ) -> SeqEnum
{Check the commutators of the filter. Return a list of the experiment.}
  G := F`Object;
  Im := Image(F);
  M := MaximalIndices(F);
  result := [];
  for i in [1..#Im-1] do
    for j in [i..#Im-1] do
      C := CommutatorSubgroup( Im[i], Im[j] );
      isit := C in Im;
      if isit then
        k := M[Index(Im,C)];
      else
        k := 0;
      end if;
      r := < [M[i],M[j]], [* isit,k *], isit >; // < indices, in F, can place in F >
      if #ConstructFilter(F,[G!C.i : i in [1..Ngens(C)]]) ne #F then
        r[3] := true;
      end if;
      Append(~result,r);
    end for;
  end for;
  return result;
end intrinsic;

/*

N := 3^7;
check3 := [];
for i in [1..NumberOfSmallGroups(N)] do
  G := SmallGroup(N,i);
  F := pCentralFilter(G);
  FF := Refine(F);
  list := CheckCommutators(FF);
  for j in [1..#list] do
    if Type(list[j][2][2]) eq RngIntElt then
      Append(~check,i);
    end if;
  end for;
end for;

*/

