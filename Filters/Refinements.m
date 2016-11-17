// This file contains programs for searching through the bimaps of the associated Lie algebra to find refinements.

import "FilterDefs.m" : __GetFilter;
import "GenerateFilter.m" : __GenerateFilter;
import "Util.m" : __IsCyclic, __IsConjugateCyclic;

//__GetActionsOnModulesOLD := function( A, u, v, w, command )
//  K := BaseRing(A); 
//  if command eq MidNucleus then
//    L := Induce(A,2);
//    M := Induce(A,1);
//    R := sub< MatrixAlgebra(K,0) | >;
//  elif command eq Centroid then
//    L := Induce(A,2);
//    M := Induce(A,1);
//    R := Induce(A,0);
//  elif command eq DerivationAlgebra then
//    L := sub< MatrixAlgebra(K,u) | [ ExtractBlock( x, 1, 1, u, u ) : x in Generators(A) ] >;
//    M := sub< MatrixAlgebra(K,v) | [ ExtractBlock( x, u+1, u+1, v, v ) : x in Generators(A) ] >;
//    R := sub< MatrixAlgebra(K,w) | [ ExtractBlock( x, u+v+1, u+v+1, w, w ) : x in Generators(A) ] >;
//  elif command eq LeftNucleus then
//    L := sub< MatrixAlgebra(K,u) | [ ExtractBlock( x, 1, 1, u, u ) : x in Generators(A) ] >;
//    M := sub< MatrixAlgebra(K,0) | >;
//    R := sub< MatrixAlgebra(K,w) | [ ExtractBlock( x, u+1, u+1, w, w ) : x in Generators(A) ] >;
//  elif command eq RightNucleus then
//    L := sub< MatrixAlgebra(K,0) | >;
//    M := sub< MatrixAlgebra(K,v) | [ Transpose(ExtractBlock( x, 1, 1, v, v )) : x in Generators(A) ] >;
//    R := sub< MatrixAlgebra(K,w) | [ ExtractBlock( x, v+1, v+1, w, w ) : x in Generators(A) ] >;
//  end if;
//  return L,M,R;
//end function;

__GetActionsOnModules := function( A, u, v, w, command )
  K := BaseRing(A);
  try
    L := Induce(A,2);
  catch err
    L := sub< MatrixAlgebra(K,0) | >;
  end try;
  try
    M := Induce(A,1);
  catch err
    M := sub< MatrixAlgebra(K,0) | >;
  end try;
  try
    R := Induce(A,0);
  catch err
    R := sub< MatrixAlgebra(K,0) | >;
  end try;
  if command eq DerivationAlgebra then
    L := sub< MatrixAlgebra(K,Degree(L)) | Basis(L) >;
    M := sub< MatrixAlgebra(K,Degree(M)) | Basis(M) >;
    R := sub< MatrixAlgebra(K,Degree(R)) | Basis(R) >;
  end if;
  return L,M,R;
end function;

__CheckJacobsonRadical := function( L, M, R )
  J := JacobsonRadical(L);
  if Dimension(J) eq 0 then
    J := JacobsonRadical(M);
    if Dimension(J) eq 0 then
      J := JacobsonRadical(R);
      if Dimension(J) eq 0 then
        return false,_,_;
      else
        i := 3;
      end if;
    else
      i := 2;
    end if;
  else
    i := 1;
  end if;
  Mod := VectorSpace( BaseRing(J), [Degree(L),Degree(M),Degree(R)][i] );
  Series := [ Mod ];
  while Dimension(Series[#Series]) gt 0 do
    S := sub< Mod | [ v*j : v in Basis(Series[#Series]), j in Basis(J) ] >;
    Append(~Series, S);
  end while;
  Remove(~Series,1);
  Prune(~Series);
  return true, i, Series;
end function;

__CheckSemisimple := function( L, M, R )
  K := BaseRing(L);
  trivial := true;
  Algs := [* L,M,R *];
  i := 0;

  while trivial and (i le 2) do
    i +:= 1;
    A := Algs[i];
    if (Dimension(A) gt 0) then // need to check dimension first because of magma
      AM := RModule(A);
      sums := IndecomposableSummands(AM);
      if #sums gt 1 then
        prims := [* Action(s) : s in sums *];
        cents := [* Center(R) : R in prims *];
        cyc_algs := [* *];
        for C in cents do
          isit,gen := __IsCyclic( C );
          assert isit;
          Append(~cyc_algs, sub< C | gen >);
        end for;
        iso_types := [ j : j in [1..#cyc_algs] | __IsConjugateCyclic( cyc_algs[1].1, cyc_algs[j] ) ];
        if #iso_types lt #sums then 
          S := &+[ sums[j] : j in iso_types ];
          VS := VectorSpace(K,Degree(A));
          return true, i, [ sub< VS | [ VS!(b @ Morphism(S,AM)) : b in Basis(S) ] > ]; 
        end if;
      end if;
    end if;
  end while;
  return false,_,_;
end function;

// Finds the bimap with a nontrivial Jacobson radical.
__FindRefinementFromBimaps := function( F, Commands )
  LA := LieAlgebra(F);
  K := BaseRing(LA);
  Bimaps := LA`GradedInfo`Bimaps;
  trivial := true;
  i := 1;
  j := 1;

  while trivial and (i le #Bimaps) do
    B := Bimaps[i];
    ChangeTensorCategory(~B,HomotopismCategory(2));
    X := Commands[j](B); // creates desired algebra
    L,M,R := __GetActionsOnModules( X, Dimension(B`Domain[1]), Dimension(B`Domain[2]), Dimension(B`Codomain), Commands[j] );

    // Extract characteristic structure.
    bool, t, ModSeq := __CheckJacobsonRadical( L, M, R );
    if not bool then
      bool, t, ModSeq := __CheckSemisimple( L, M, R );
      if bool then location := "semi"; end if;
    else
      location := "rad";
    end if;

    if bool then
      trivial := false;
    end if;

    // If we found nothing, then we exhaust the bimaps and leave the loop.
    if trivial then
      if j eq #Commands then
        i +:= 1;
        j := 1;
      else  
        j +:= 1;
      end if;
    end if;
  end while;

  if trivial then
    return false, _, _, _;
  end if;

  // At this stage, we have something to work with.
  BF := BoundaryFilter(F);
  Spaces := B`Domain cat [* B`Codomain *];
  temp := LA`GradedInfo`BimapIndices[i];
  temp := < temp[1], temp[2], [ temp[1][k] + temp[2][k] : k in [1..#temp[1]] ] >;
  oldindex := temp[t];
  h_comp := Index(LA`GradedInfo`HomogeneousIndices,oldindex);
  pi := LA`GradedInfo`Projections[h_comp];
  phi := F`Lie_Func;

  // Figure out where the refinement came from
  which := < <temp[1],temp[2]>, "" >;
  if Commands[j] eq DerivationAlgebra then which[2] cat:= "derivation";
  elif Commands[j] eq MidNucleus then which[2] cat:= "adjoint";
  elif Commands[j] eq LeftNucleus then which[2] cat:= "left nucleus";
  elif Commands[j] eq RightNucleus then which[2] cat:= "right nucleus";
  elif Commands[j] eq Centroid then which[2] cat:= "centroid"; end if;
  if location eq "rad" then
    which[2] cat:= ": radical";
  else
    which[2] cat:= ": semisimple";
  end if;

  Grps := [];
  for S in ModSeq do
    gens := [ ((Spaces[t]!b) @@ pi) @@ phi : b in Basis(S) ];
    Append(~Grps, sub< F`Object | gens, oldindex @ BF >); 
  end for;

  // Initialize the prefilter
  if F`Lex_Order then
    PO := function(x,y)
      i := 1;
      while i le #x do
        if x[i] lt y[i] then
          return true;
        elif x[i] gt y[i] then
          return false;
        end if;
        i +:= 1;
      end while;
      return true;
    end function; 
  else
    PO := function(x,y)
      if F`Preorder(Prune(x),Prune(y)) then
        if F`Preorder(Prune(y),Prune(x)) then 
          return x[#x] le y[#y];
        else
          return true;
        end if;
      end if;
      return false;
    end function;
  end if;
  old_inds := F`Indices;
  j := Index(old_inds, oldindex);
  new_inds := [ Append(seq,0) : seq in old_inds[1..j] ] cat [ Append(oldindex,k) : k in [1..#ModSeq] ] 
              cat [ Append(seq,0) : seq in old_inds[j+1..#old_inds] ];
  image := Image(F)[1..j] cat Grps cat Image(F)[j+1..#Image(F)];
  FF := __GenerateFilter( image, new_inds, PO : LexOrder := F`Lex_Order );

  return true, FF, which;
end function;


// intrinsics -----------------------------------------------------------------

intrinsic Refine( F::Flt : Heuristics := ["all"], Iterations := 0 ) -> Flt, SeqEnum
{Returns a refinement of the totally ordered filter F and a sequence cataloging the refinements used and which bimaps were used.
Set Iterations to a positive integer to set the cutoff on the number of iterations. Otherwise, set to 0, which is the default.
Set the sequence Heuristics to allow the kinds of heuristics the algorithm uses. The default includes everything.}
  require (Type(Heuristics) eq SeqEnum) and (Type(Universe(Heuristics)) eq MonStg) : "Unknown heuristics.";
  if Heuristics eq ["all"] then
    Heuristics := ["derivation", "adjoint", "left nucleus", "right nucleus", "centroid" ];
  end if;
  require (Type(Iterations) eq RngIntElt) and Iterations ge 0 : "Iterations must be set to a nonnegative integer.";
  require Heuristics subset ["derivation", "adjoint", "left nucleus", "right nucleus", "centroid" ] : "Unknown heuristic.";
  require #Heuristics gt 0 : "Heuristics must be nonempty.";
  require F`Totally_Ordered : "Filter must be totally ordered.";

  Commands := [* *];
  for h in Heuristics do
    if h eq "derivation" then Append(~Commands, DerivationAlgebra);
    elif h eq "adjoint" then Append(~Commands, MidNucleus);
    elif h eq "left nucleus" then Append(~Commands, LeftNucleus);
    elif h eq "right nucleus" then Append(~Commands, RightNucleus);
    elif h eq "centroid" then Append(~Commands, Centroid); end if;
  end for;

  Catalog := [];
  found, FFF, which := __FindRefinementFromBimaps( F, Commands );
  i := 1;
  if not found then
    return F,_;
  end if;

  if Iterations eq 0 then
    repeat 
      FF := FFF;
      Append(~Catalog, which);
      found, FFF, which := __FindRefinementFromBimaps( FF, Commands );
    until not found;
  elif Iterations eq 1 then
    Catalog := [which];
    FF := FFF;
  elif Iterations gt 1 then
    repeat 
      FF := FFF;
      Append(~Catalog, which);
      found, FFF, which := __FindRefinementFromBimaps( FF, Commands );
      i +:= 1;
    until (not found) or (i eq Iterations);
  end if;
  return FF, Catalog;
end intrinsic;

intrinsic AdjointRefinement( F::Flt ) -> Flt
{Computes the adjoint refinement of F. If no such refinement exists, the original filter is returned.}
  require F`Totally_Ordered : "Filter must be totally ordered.";
  return Refine( F : Iterations := 1, Heuristics := ["adjoint"] );
end intrinsic;

intrinsic CentroidRefinement( F::Flt ) -> Flt
{Computes the centroid refinement of F. If no such refinement exists, the original filter is returned.}
  require F`Totally_Ordered : "Filter must be totally ordered.";
  return Refine( F : Iterations := 1, Heuristics := ["centroid"] );
end intrinsic;

intrinsic DerivationRefinement( F::Flt ) -> Flt
{Computes the derivation refinement of F. If no such refinement exists, the original filter is returned.}
  require F`Totally_Ordered : "Filter must be totally ordered.";
  return Refine( F : Iterations := 1, Heuristics := ["derivation"] );
end intrinsic;

intrinsic LeftNucleusRefinement( F::Flt ) -> Flt
{Computes the left scalar refinement of F. If no such refinement exists, the original filter is returned.}
  require F`Totally_Ordered : "Filter must be totally ordered.";
  return Refine( F : Iterations := 1, Heuristics := ["left nucleus"] );
end intrinsic;

intrinsic RightNucleusRefinement( F::Flt ) -> Flt
{Computes the right scalars refinement of F. If no such refinement exists, the original filter is returned.}
  require F`Totally_Ordered : "Filter must be totally ordered.";
  return Refine( F : Iterations := 1, Heuristics := ["right nucleus"] );
end intrinsic;
