/* 
    Copyright 2016, 2017, Joshua Maglione, James B. Wilson.
    Distributed under GNU GPLv3.
*/


/*
  This file contains all the low-level definitions for tensor categories (TenCat).
*/


// ------------------------------------------------------------------------------
//                                      Print
// ------------------------------------------------------------------------------
intrinsic Print( C::TenCat )
{Print C}
  if C`Contra then
    s := "Cotensor category of valence ";
  else
    s := "Tensor category of valence ";
  end if;
  s cat:= Sprintf( "%o (", C`Valence );
  a := C`Arrows;
  i := C`Valence-1;
  while i ge 0 do
    s cat:= ( i @ a eq 1 ) select "->" else (i @ a eq -1) select "<-" else "==";
    i -:= 1;
    s cat:= (i eq -1) select ")" else ",";
  end while;
  
  P := C`Repeats;
  i := #P;
  s cat:= " (";
  for X in P do
  	s cat:= Sprintf( "%o", X);
    i -:= 1;
    s cat:= (i eq 0) select ")" else ",";
  end for;

  printf s;
end intrinsic;

// ------------------------------------------------------------------------------
//                                    Compare
// ------------------------------------------------------------------------------
intrinsic 'eq'(C1::TenCat, C2::TenCat) -> BoolElt
{C1 eq C2}
  return (C1`Valence eq C2`Valence) and (C1`Repeats eq C2`Repeats) and forall{ x : x in Domain(C1`Arrows) | (x @ C1`Arrows) eq (x @ C2`Arrows) };
end intrinsic;
