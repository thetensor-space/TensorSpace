import "FilterDefs.m" : __GetFilter;

intrinsic Length( F::Flt ) -> RngIntElt
{Returns the length of F.}
  if assigned F`Length then
    return F`Length;
  end if;
  if F`Totally_Ordered then
    F`Length := #F`Image-1;
  else
    L := Lattice(F);
    F`Length := Diameter(L)-1;
  end if;
  return F`Length;
end intrinsic;

intrinsic '#'( F::Flt ) -> RngIntElt
{Returns the size of the image.}
  return #(F`Image);
end intrinsic;

intrinsic Image( F::Flt ) -> SeqEnum
{Returns the image of F.}
  return F`Image;
end intrinsic;

intrinsic MaximalIndices( F::Flt ) -> SeqEnum
{Returns the maximal indices of the filter F, provided they exist.}
  require F`Max_Inds : "Unknown if maximal indices exist.";
  return F`Indices;
end intrinsic;

intrinsic Preorder( F::Flt ) -> UserProgram
{Returns the preorder function used for F.}
  return F`Preorder;
end intrinsic;

intrinsic IsSeries( F::Flt ) -> BoolElt
{Determines if F is a series.}
  if assigned F`Totally_Ordered then
    return F`Totally_Ordered;
  end if;
  L := Lattice( F );
  return IsTree( L );
end intrinsic;

intrinsic Lattice( F::Flt ) -> GrphDir
{Returns the lattice of F as a directed graph.
Each vertex is a subgroup in the image.} //assumed groups
  if assigned F`Lattice then
    return F`Lattice;
  end if;
  im := Image(F);
  n := #im;
  edges := [];
  for i in [1..n-1] do
    S := [ s : s in F`Indices | F`Indices[i] ne s and F`Preorder( F`Indices[i], s ) ];
    if #S eq 0 then
      Append(~edges, [i,n]);
    else
      while exists(s){ s : s in S | exists{ t : t in S | t ne s and F`Preorder( t, s ) } } do
        Remove(~S,Index(S,s));
      end while;
      for s in S do
        Append(~edges, [i,Index(F`Indices,s)]);
      end for;
    end if;
  end for;
  G := Digraph< n | edges >;
  F`Lattice := G;
  return G;
end intrinsic;

intrinsic BoundaryFilter( F::Flt ) -> Flt
{Returns the boundary filter of F.}
  if assigned F`Boundary then
    return F`Boundary;
  end if;
  if assigned F`Totally_Ordered and F`Totally_Ordered and F`Max_Inds then
    Im := Image(F);
    Inds := [ [0 : i in [1..F`Domain]] ] cat Prune(F`Indices);
    TO := true;
  else
    L := Lattice(F);
    Im := [ F`Object ];
    Inds := [ [0 : i in [1..F`Domain]] ] cat Prune(F`Indices);
    for v in Prune([ v : v in Vertices(L)]) do
      A := {@ u : u in Vertices(L) | v adj u @};
      H := sub< F`Object | [ Image(F)[Index( Vertices(L), a )] : a in A ] >;
      Append(~Im,H);
    end for;
    TO := 0;
  end if;
  B := __GetFilter( F`Object, Inds, Im, F`Preorder : TotallyOrdered := TO, MaxInds := false );
  F`Boundary := B;
  return B;
end intrinsic;
