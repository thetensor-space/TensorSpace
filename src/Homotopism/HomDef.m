/* 
    Copyright 2016, 2017, Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


/*
  This file contains all the low-level definitions for homotopisms (Hmtp).
*/


import "Hom.m" : __GetHomotopism;
// ------------------------------------------------------------------------------
//                                     Print
// ------------------------------------------------------------------------------
intrinsic Print( H::Hmtp )
{Print H}
  A := H`Cat`Arrows;
  v := H`Cat`Valence;
  s := Sprintf( "Maps from " );
  for i in [2..v-1] do
    s cat:= Sprintf( "U%o x ", v-i+1 );
  end for;
  s cat:= Sprintf( "U1 >-> U0 to " );
  for i in [2..v-1] do
    s cat:= Sprintf( "V%o x ", v-i+1 );
  end for;
  s cat:= Sprintf( "V1 >-> V0." );
  for i in Reverse([1..v-1]) do
    if ISA(Type(H`Maps[v-i]),Mtrx) then
      u := "\n";
    else
      u := "";
    end if;
    if i @ A eq 1 then
      s cat:= Sprintf( "\nU%o -> V%o: " cat u cat "%o", i, i, H`Maps[v-i] );
    elif i @ A eq -1 then
      s cat:= Sprintf( "\nU%o <- V%o: " cat u cat "%o", i, i, H`Maps[v-i] );
    else
      s cat:= Sprintf( "\nU%o == V%o: " cat u cat "%o", i, i, H`Maps[v-i] );
    end if;
  end for;
  if ISA(Type(H`Maps[v]),Mtrx) then
    u := "\n";
  else
    u := "";
  end if;
  if H`Cat`Contra then
    printf s;
  else
    if 0 @ A eq 1 then
      printf s cat Sprintf( "\nU0 -> V0: " cat u cat "%o", H`Maps[v] );
    elif 0 @ A eq -1 then
      printf s cat Sprintf( "\nU0 <- V0: " cat u cat "%o", H`Maps[v] );
    else
      printf s cat Sprintf( "\nU0 == V0: " cat u cat "%o", H`Maps[v] );
    end if;
  end if;
end intrinsic;

// ------------------------------------------------------------------------------
//                                   Composition
// ------------------------------------------------------------------------------
intrinsic '*'( H1::Hmtp, H2::Hmtp ) -> Hmtp
{H1 * H2}
  dom := H1`Domain;
  cod := H2`Codomain;
  require H1`Cat eq H2`Cat: "Categories are incompatible.";
  M := [* *];
  for i in Reverse([0..dom`Valence-1]) do
    if i @ H1`Cat`Arrows eq -1 then
      f := H2`Maps[dom`Valence-i];
      g := H1`Maps[dom`Valence-i];
    else
      f := H1`Maps[dom`Valence-i];
      g := H2`Maps[dom`Valence-i];
    end if;
    try
      Append(~M,f*g);
    catch err
      error "Cannot compose maps.";
    end try;
  end for;
  return __GetHomotopism( H1`Cat, M : Cod := cod, Dom := dom );
end intrinsic;
