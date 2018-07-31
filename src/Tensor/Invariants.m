/* 
    Copyright 2016--2018 Joshua Maglione, James B. Wilson.
    Distributed under GNU GPLv3.
*/


/*
  This file contains invariants for tensors. They come in two flavors: linear
  algebra and polynomial-based invariants. Most of the invariants have been 
  optimized for bimaps (3-tensors).
*/


import "Tensor.m" : __GetTensor, __TensorOnVectorSpaces;
import "TensorData.m" : __GetForms;
import "../TensorCategory/Hom.m" : __GetHomotopism;
import "../GlobalVars.m" : __LIST, __SANITY_CHECK, __FRAME;
import "../Util/ConjugateCyclic.m" : __IsCyclic;

// Given vectors return blocks
__VectorToBlocks := function( v, d )
  F := BaseRing( v );
  v := Eltseq( v );
  return <MatrixAlgebra( F, d[i] )![ v[ &+([0] cat [ d[j]^2 : j in [1..i-1] ]) \
    + k] : k in [1..d[i]^2] ] : i in [1..#d]>;
end function;


// A function to remove superfluous blocks for fused coordinates. 
__ReduceByFuse := function(basis, partition, coords)
  K := BaseRing(basis[1][1]);
  toFuse := [S : S in partition | #S gt 1];
  newBasis := basis;
  for S in toFuse do
    T := S diff {Max(S)};
    for t in T do
      if t in coords then
        i := Index(coords);
        temp := [];
        for B in newBasis do
          blocks := B;
          blocks[i] := IdentityMatrix(K, 0);
          Append(~temp, blocks);
        end for;
        newBasis := temp;
      end if;
    end for;
  end for;
  return newBasis;
end function;


__SCentroid := function( t, S )
  S := Sort([ s : s in S ]);
  C := Basis( t`Codomain );
  d := #C;
  R := BaseRing( t`Codomain );
  B := CartesianProduct( < [1..Dimension(X)] : X in t`Domain > );
  dims := [ Dimension( t`Domain[s] ) : s in S ];
  V := RSpace( R, &+[ d^2 : d in dims ] + d^2 );
  mat := [];

  vprint eMAGma, 1 : "Setting up linear system: " cat \
    IntegerToString(Dimension(V)) cat " by " cat IntegerToString(&*dims*d*#S);

  for x in B do
    for k in [1..d] do
      r := V!0; 
      for i in [1..d] do
        temp := [ x[l] : l in [1..#x] ] cat [i];
        r[ &+[ d^2 : d in dims ] + k + (i-1)*d ] -:= Slice(t, [{l} : \
          l in temp])[1];
      end for;
      rows := [ r : i in [1..#S] ];
      for i in [1..#S] do
        for j in [1..dims[i]] do
          temp := [ x[l] : l in [1..#x] ] cat [k];
          temp[S[i]] := j;
          rows[i][ &+([ dims[x]^2 : x in [1..i-1] ] cat [0]) \
            + (x[S[i]]-1)*dims[i] + j ] +:= Slice(t, [{l} : l in temp])[1];
        end for;
      end for;
      mat cat:= rows;
    end for;
  end for;
  M := Matrix(mat);

  vprint eMAGma, 1 : "Solving linear system: " cat IntegerToString(Ncols(M)) \
    cat " by " cat IntegerToString(Nrows(M));

  N := NullspaceOfTranspose(M);
  basis := [__VectorToBlocks(b, dims cat [d]) : b in Basis(N)];
  return __ReduceByFuse(basis, RepeatPartition(TensorCategory(t)), \
    Reverse(Sort([s : s in S])) cat [0]);
end function;

__Derivations := function( t )
  B := CartesianProduct( < [1..Dimension(X)] : X in t`Domain > );
  C := Basis( t`Codomain );
  d := #C;
  R := BaseRing( t`Codomain );
  dims := [ Dimension( X ) : X in t`Domain ];
  V := RSpace( R, &+[ d^2 : d in dims ] + d^2 );
  mat := [];

  vprint eMAGma, 1 : "Setting up linear system: " cat \
    IntegerToString(Dimension(V)) cat " by " cat IntegerToString(&*dims*d);

  for x in B do
    for k in [1..d] do
      r := V!0; 
      for i in [1..d] do
        temp := [ x[l] : l in [1..#x] ] cat [i];
        r[ &+[ d^2 : d in dims ] + k + (i-1)*d ] -:= Slice(t, [{l} : \
          l in temp])[1]; 
      end for;
      for i in [1..#dims] do
        for j in [1..dims[i]] do
          temp := [ x[l] : l in [1..#x] ] cat [k];
          temp[i] := j; // represents the endomorphism from x[i] to e_j 
          r[&+([dims[l]^2 : l in [1..i-1]] cat [0]) + (x[i]-1)*dims[i] + j] \
            +:= Slice(t, [{l} : l in temp])[1];
        end for;
      end for;
      Append(~mat,r);
    end for;
  end for;
  M := Matrix(mat);

  vprint eMAGma, 1 : "Solving linear system: " cat IntegerToString(Ncols(M)) \
    cat " by " cat IntegerToString(Nrows(M));

  N := NullspaceOfTranspose(M);
  basis := [__VectorToBlocks(b, dims cat [d]) : b in Basis(N)];
  return __ReduceByFuse(basis, RepeatPartition(TensorCategory(t)), \
    Reverse([0..#Domain(t)]));
end function;

// Computes the nucleus of the first two terms. 
__21Nucleus := function( t )
  I := CartesianProduct( < [1..Dimension(X)] : X in t`Domain > );
  V2 := t`Domain[1];
  V1 := t`Domain[2];
  R := BaseRing(V2);
  d2 := Dimension(V2);
  d1 := Dimension(V1);
  V := RSpace(R, d2^2 + d1^2);
  mat := [];

  vprint eMAGma, 1 : "Setting up linear system: " cat \
    IntegerToString(Dimension(V)) cat " by " cat \
    IntegerToString(#I*Dimension(t`Codomain));

  for x in I do
    for k in [1..Dimension(t`Codomain)] do
      r := V!0;
      temp := [ x[l] : l in [1..#x] ];
      for i in [1..d2] do
        temp[1] := i;
        r[ (x[1]-1)*d2 + i ] +:= Slice(t, [{l} : l in temp] cat [{k}])[1]; 
      end for;
      temp := [ x[l] : l in [1..#x] ];
      for j in [1..d1] do
        temp[2] := j;
        r[ d2^2 + (x[2]-1)*d1 + j ] -:= Slice(t, [{l} : l in temp] cat [{k}])[1];
      end for;
      Append(~mat,r);
    end for;
  end for;
  M := Matrix(mat);

  vprint eMAGma, 1 : "Solving linear system: " cat IntegerToString(Ncols(M)) \
    cat " by " cat IntegerToString(Nrows(M));

  T := NullspaceOfTranspose(M);
  blocks := [__VectorToBlocks(T.i, [d2, d1]) : i in [1..Dimension(T)]];
  basis := [<b[1], Transpose(b[2])> : b in blocks];  
  return basis;
end function;


/* 
  Below are functions optimized for bimaps.
    They use array copy which is much faster than what is done above. 

    They all take a tensor t and return a sequence of tuples of matrices 
    corresponding to the basis of the matrix vector space satisfying the linear
    equations. 
*/

__MidNucleusOfBimap := function( t )
  a := Dimension(t`Domain[1]);
  b := Dimension(t`Domain[2]);
  c := Dimension(t`Codomain);
  S := StructureConstants(t);
  K := BaseRing(t);
  // t : K^a x K^b >-> K^c given by S

  vprint eMAGma, 1 : "Setting up linear system: " cat IntegerToString(a^2+b^2) \
    cat " by " cat IntegerToString(a*b*c);

  M := ZeroMatrix(K,a^2+b^2,a*b*c);

  // Put the A blocks in
  Fa := Foliation(t, 2);
  ipos := b^2+1;
  jpos := 1;
  for i in [1..a] do
    InsertBlock( ~M, Fa, ipos, jpos );
    ipos +:= a;
    jpos +:= b*c;
  end for;
  delete Fa;

  // Put the B blocks in
  Fb := Transpose(Foliation(t, 1));
  Fb_blocks := [ -Transpose(Matrix(Fb[(i-1)*c+1..i*c])) : i in [1..a] ];
  delete Fb;
  jpos := 1;
  for i in [1..a] do
    ipos := 1;
    for j in [1..b] do
      InsertBlock( ~M, Fb_blocks[1], ipos, jpos );
      ipos +:= b;
      jpos +:= c;
    end for;
    Remove(~Fb_blocks,1);
  end for;

  vprint eMAGma, 1 : "Solving linear system: " cat IntegerToString(Nrows(M)) \
    cat " by " cat IntegerToString(Ncols(M));

  N := NullspaceMatrix(M);
  basis := [<Matrix(a, a, Eltseq(N[i])[b^2+1..a^2+b^2]), Transpose(Matrix(b, \
    b, Eltseq(N[i])[1..b^2]))> : i in [1..Nrows(N)]];
  return basis;
end function;

__LeftNucleusOfBimap := function( t )
  a := Dimension(t`Domain[1]);
  b := Dimension(t`Domain[2]);
  c := Dimension(t`Codomain);
  S := StructureConstants(t);
  K := BaseRing(t);
  // t : K^a x K^b >-> K^c given by S

  vprint eMAGma, 1 : "Setting up linear system: " cat IntegerToString(a^2+c^2) \
    cat " by " cat IntegerToString(a*b*c);

  M := ZeroMatrix(K,a^2+c^2,a*b*c);

  // Put the A blocks in
  Fa := HorizontalJoin( __GetForms(S, [a,b,c], 2, 1) );
  ipos := c^2+1;
  jpos := 1;
  for i in [1..a] do
    InsertBlock( ~M, Fa, ipos, jpos );
    ipos +:= a;
    jpos +:= b*c;
  end for;
  delete Fa;

  // Put the B blocks in
  Fb := __GetForms(S, [a,b,c], 1, 0 : op := true);
  jpos := 1;
  for i in [1..a] do
    ipos := 1;
    block := -Fb[i];
    for j in [1..c] do
      InsertBlock( ~M, block, ipos, jpos );
      ipos +:= c;
      jpos +:= b;
    end for;
  end for;
  delete Fb;

  vprint eMAGma, 1 : "Solving linear system: " cat IntegerToString(Nrows(M)) \
    cat " by " cat IntegerToString(Ncols(M));

  N := NullspaceMatrix(M);
  basis := [<Transpose(Matrix(a, a, Eltseq(N[i])[c^2+1..a^2+c^2])), Matrix(c, \
    c, Eltseq(N[i])[1..c^2])> : i in [1..Nrows(N)]];
  return basis;
end function;

__RightNucleusOfBimap := function( t )
  a := Dimension(t`Domain[1]);
  b := Dimension(t`Domain[2]);
  c := Dimension(t`Codomain);
  S := StructureConstants(t);
  K := BaseRing(t);
  // t : K^a x K^b >-> K^c given by S

  vprint eMAGma, 1 : "Setting up linear system: " cat IntegerToString(b^2+c^2) \
    cat " by " cat IntegerToString(a*b*c);

  M := ZeroMatrix(K,b^2+c^2,a*b*c);

  // Put the A blocks in
  Fa := -HorizontalJoin( __GetForms(S, [a,b,c], 2, 1 : op := true) );
  ipos := c^2+1;
  jpos := 1;
  for i in [1..b] do
    InsertBlock( ~M, Fa, ipos, jpos );
    ipos +:= b;
    jpos +:= a*c;
  end for;
  delete Fa;

  // Put the B blocks in
  Fb := __GetForms(S, [a,b,c], 2, 0 : op := true);
  jpos := 1;
  for i in [1..b] do
    ipos := 1;
    block := Fb[i];
    for j in [1..c] do
      InsertBlock( ~M, block, ipos, jpos );
      ipos +:= c;
      jpos +:= a;
    end for;
  end for;
  delete Fb;

  vprint eMAGma, 1 : "Solving linear system: " cat IntegerToString(Nrows(M)) \
    cat " by " cat IntegerToString(Ncols(M));

  N := NullspaceMatrix(M);
  basis := [<Matrix(b, b, Eltseq(N[i])[c^2+1..b^2+c^2]), Transpose(Matrix(c, \
    c, Eltseq(N[i])[1..c^2]))> : i in [1..Nrows(N)]];
  return basis;
end function;

__CentroidOfBimap := function(t)
  a := Dimension(t`Domain[1]);
  b := Dimension(t`Domain[2]);
  c := Dimension(t`Codomain);
  S := StructureConstants(t);
  K := BaseRing(t);
  // t : K^a x K^b >-> K^c given by S

  vprint eMAGma, 1 : "Setting up linear system: " cat IntegerToString(a^2+b^2+c^2) cat " by " cat IntegerToString(2*a*b*c);

  M := ZeroMatrix(K, a^2+b^2+c^2, 2*a*b*c);

  // Adjoint blocks:
  // Put the A blocks in
  Fa := Foliation(t, 2);
  ipos := b^2+1;
  jpos := 1;
  for i in [1..a] do
    InsertBlock( ~M, Fa, ipos, jpos );
    ipos +:= a;
    jpos +:= b*c;
  end for;
  delete Fa;

  // Put the B blocks in
  Fb := Transpose(Foliation(t, 1));
  Fb_blocks := [ Transpose(Matrix(Fb[(i-1)*c+1..i*c])) : i in [1..a] ];
  delete Fb;
  jpos := 1;
  for i in [1..a] do
    ipos := 1;
    for j in [1..b] do
      InsertBlock( ~M, Fb_blocks[1], ipos, jpos );
      ipos +:= b;
      jpos +:= c;
    end for;
    Remove(~Fb_blocks,1);
  end for;

  // Left Scalars:
  // Put the A blocks in
  Fa := HorizontalJoin( __GetForms(S, [a,b,c], 2, 1) );
  ipos := b^2+1;
  jpos := a*b*c+1;
  for i in [1..a] do
    InsertBlock( ~M, Fa, ipos, jpos );
    ipos +:= a;
    jpos +:= b*c;
  end for;
  delete Fa; 

  // Put the B blocks in
  Fb := __GetForms(S, [a,b,c], 1, 0 : op := true);
  jpos := a*b*c+1;
  for i in [1..a] do
    ipos := a^2+b^2+1;
    block := Fb[i];
    for j in [1..c] do
      InsertBlock( ~M, block, ipos, jpos );
      ipos +:= c;
      jpos +:= b;
    end for;
  end for;
  delete Fb; 

  // add block for the fuse
  w := [b^2,0,a^2+b^2];
  if exists(S){ S : S in t`Cat`Repeats | #S ge 2 } then
    S := { 3-x : x in S };
    if S eq {2,3} then k := -1; else k := 1; end if;
    inds := [a,b,c];
    assert forall{ s : s in S | inds[s] eq inds[Maximum(S)] };
    offset := [ b^2+1,1,a^2+b^2+1 ];
    s := Minimum(S);
    Exclude(~S,s);
    while #S gt 0 do
      m := Maximum(S);
      Exclude(~S,m);
      if m eq 3 then
        perm := Eltseq(Transpose(Matrix(IntegerRing(),c,c,[1..c^2])));
        N := PermutationMatrix(K,perm);
      else
        N := IdentityMatrix(K,inds[m]^2);
      end if;
      X := ZeroMatrix(K,a^2+b^2+c^2,inds[s]^2);
      InsertBlock(~X,k*IdentityMatrix(K,inds[s]^2),offset[s],1);
      InsertBlock(~X,N,offset[m],1);
      M := HorizontalJoin(X,M);
    end while;
  end if;

  vprint eMAGma, 1 : "Solving linear system: " cat IntegerToString(Nrows(M)) \
    cat " by " cat IntegerToString(Ncols(M));

  /* Eventually fix this to not have to multiply matrices. */
  D := DiagonalMatrix(K, [1 : i in [1..b^2]] cat [-1 : i in [1..a^2]] cat \
    [1 : i in [1..c^2]]);
  N := NullspaceMatrix(D*M);
  basis := [<Matrix(a, a, Eltseq(N[i])[w[1]+1..w[1]+a^2]), Matrix(b, b, \
    Eltseq(N[i])[w[2]+1..w[2]+b^2]), Transpose(Matrix(c, c, \
    Eltseq(N[i])[w[3]+1..w[3]+c^2]))> : i in [1..Nrows(N)]];
  return __ReduceByFuse(basis, RepeatPartition(TensorCategory(t)), \
    Reverse([0..2]));
end function;

__DerivationsOfBimap := function(t)
  a := Dimension(t`Domain[1]);
  b := Dimension(t`Domain[2]);
  c := Dimension(t`Codomain);
  S := StructureConstants(t);
  K := BaseRing(t);
  // t : K^a x K^b >-> K^c given by S

  vprint eMAGma, 1 : "Setting up linear system: " cat \
    IntegerToString(a^2+b^2+c^2) cat " by " cat IntegerToString(a*b*c);

  M := ZeroMatrix(K,a^2+b^2+c^2,a*b*c);

  // Put the A blocks in
  Fa := Foliation(t, 2);
  ipos := b^2+1;
  jpos := 1;
  for i in [1..a] do
    InsertBlock( ~M, Fa, ipos, jpos );
    ipos +:= a;
    jpos +:= b*c;
  end for;
  delete Fa;

  // Put the B blocks in
  Fb := Transpose(Foliation(t, 1));
  Fb_blocks := [ Transpose(Matrix(Fb[(i-1)*c+1..i*c])) : i in [1..a] ];
  delete Fb;
  jpos := 1;
  for i in [1..a] do
    ipos := 1;
    for j in [1..b] do
      InsertBlock( ~M, Fb_blocks[1], ipos, jpos );
      ipos +:= b;
      jpos +:= c;
    end for;
    Remove(~Fb_blocks,1);
  end for;

  // Put the C blocks in
  Fc := Transpose(Foliation(t, 0));
  jpos := 1;
  for i in [1..a*b] do
    ipos := a^2+b^2+1;
    block := Transpose(Matrix( Fc[i] ));
    for j in [1..c] do
      InsertBlock( ~M, block, ipos, jpos );
      jpos +:= 1;
      ipos +:= c;
    end for;
  end for;
  delete Fc;

  // add block for the fuse
  if exists(S){ S : S in t`Cat`Repeats | #S ge 2 } then
    S := { 3-x : x in S };
    inds := [a,b,c];
    assert forall{ s : s in S | inds[s] eq inds[Maximum(S)] };
    offset := [ b^2+1,1,a^2+b^2+1 ];
    s := Maximum(S);
    Exclude(~S,s);
    if s eq 3 then 
      perm := Eltseq(Transpose(Matrix(IntegerRing(),c,c,[1..c^2])));
      N := PermutationMatrix(K,perm);
    else 
      N := -IdentityMatrix(K,inds[s]^2); 
    end if;
    while #S gt 0 do
      m := Maximum(S);
      Exclude(~S,m);
      X := ZeroMatrix(K,a^2+b^2+c^2,inds[s]^2);
      InsertBlock(~X,N,offset[s],1);
      InsertBlock(~X,IdentityMatrix(K,inds[m]^2),offset[m],1);
      M := HorizontalJoin(X,M);
    end while;
  end if;

  vprint eMAGma, 1 : "Solving up linear system: " cat \
    IntegerToString(Nrows(M)) cat " by " cat IntegerToString(Ncols(M));

  /* Eventually fix this to not have to multiply matrices. */
  D := DiagonalMatrix(K, [1 : i in [1..a^2+b^2]] cat [-1 : i in [1..c^2]]);
  N := NullspaceMatrix(D*M);
  basis := [<Matrix(a, a, Eltseq(N[i])[b^2+1..a^2+b^2]), Matrix(b, b, \
    Eltseq(N[i])[1..b^2]), Transpose(Matrix(c, c, \
    Eltseq(N[i])[a^2+b^2+1..a^2+b^2+c^2]))> : i in [1..Nrows(N)]];
  return __ReduceByFuse(basis, RepeatPartition(TensorCategory(t)), \
    Reverse([0..2]));
end function;

/* 
  Kantor's Lemma as described in Brooksbank, Wilson, "The module isomorphism 
    problem reconsidered, 2015.
  Given isomorphic field extensions E and F of a common field k, return the 
    isomorphisms from E to F and F to E.
*/
__GetFieldHom := function( E, F )
  f := DefiningPolynomial(E);
  R := PolynomialRing(F);
  factors := Factorization(R!f);
  assert exists(p){ g[1] : g in factors | Degree(g[1]) eq 1 };
  p := LeadingCoefficient(p)^-1 * p;
  phi := hom< E -> F | R.1-p >;
  g := DefiningPolynomial(F);
  R := PolynomialRing(E);
  factors := Factorization(R!g);
  i := 1;
  repeat 
    q := LeadingCoefficient(factors[i][1])^-1 * factors[i][1];
    phi_inv := hom< F -> E | R.1-q >;
    i +:= 1;
  until (E.1 @ phi) @ phi_inv eq E.1 and (F.1 @ phi_inv) @ phi eq F.1;
  return phi, phi_inv;
end function;

// A function to reduce the number of generators of a group or algebra.
__GetSmallerRandomGenerators := function( X ) 
  if not IsFinite(BaseRing(X)) then
    return X;
  end if;
  gens := Generators(X);
  if #gens le 3 then
    return X;
  end if;
  small := {};
  repeat
    Include(~small,Random(X));
    S := sub< X | small>;
  until Dimension(X) eq Dimension(S);
  return S;
end function;


// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                   Intrinsics
// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
// ==============================================================================
//                             Linear algebra methods
// ==============================================================================
intrinsic Radical( t::TenSpcElt, a::RngIntElt ) -> ModTupRng
{Returns the ith radical of t contained in Vi.}
  v := #t`Domain;
  require a ge 1 : "Argument must be a positive integer.";
  require a le v : "Argument exceeds coordinates in the domain.";
  require ISA(Type(BaseRing(t)),Fld) : "Radicals only implemented for tensors over fields.";
  if Type(t`Radicals[v-a+1]) ne RngIntElt then
    return t`Radicals[v-a+1];
  end if;

  try 
    F := Foliation(t,a);
  catch err
    error "Cannot compute structure constants.";
  end try;

  D := t`Domain[v-a+1];
  B := Basis(D);
  V := VectorSpace(BaseRing(t),#B);
  vprint eMAGma, 1 : "Solving linear system " cat IntegerToString(Nrows(F)) cat " by " cat IntegerToString(Ncols(F));
  R := Nullspace(F);
  
  if __SANITY_CHECK then
    printf "Sanity check turned on... (Radical)";
    _, tvs := __TensorOnVectorSpaces(t);
    for j in [1..10] do
      x := < Random(X) : X in tvs`Domain >;
      x[v-a+1] := Random(R);
      assert x @ tvs eq tvs`Codomain!0;
    end for;
    printf "  DONE!\n";
  end if;
  t`Radicals[v-a+1] := R;
  return R;
end intrinsic;

intrinsic Coradical( t::TenSpcElt ) -> ModTupRng, Map
{Returns the coradical of t.}
  if Type(t`Radicals[t`Valence]) ne RngIntElt then
    return t`Radicals[t`Valence][1],t`Radicals[t`Valence][2];
  end if;
  require Type(t`Codomain) in __LIST : "Codomain not a vector space.";
  I := Image(t);
  C, pi := t`Codomain/I;
  t`Radicals[t`Valence] := <C, pi>;
  return C, pi;
end intrinsic;

intrinsic Radical( t::TenSpcElt ) -> Tup
{Returns the radical of t.}
  return < Radical(t,i) : i in Reverse([1..#t`Domain]) >;
end intrinsic;

intrinsic Centroid( t::TenSpcElt ) -> AlgMat
{Returns the centroid of the tensor t.}
  if Type(t`Centroids[2][1]) ne RngIntElt then
    return t`Centroids[2][1];
  end if;
  try
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;
  if t`Valence eq 3 then
    basis := __CentroidOfBimap( t );
  else
    basis := __SCentroid( t, {1..#t`Domain} );
  end if;
  basis := [DiagonalJoin(T) : T in basis];
  MA := MatrixAlgebra(BaseRing(basis[1]), Nrows(basis[1]));
  C := sub< MA | basis >;
  C := __GetSmallerRandomGenerators(C);
  C`DerivedFrom := <t, [1..t`Valence]>; 

  if __SANITY_CHECK then
    printf "Sanity check turned on... (Centroid)";
    spaces := __FRAME(t);
    dims := [Dimension(X) : X in spaces];
    proj := [*Induce(C, a) : a in Reverse([0..t`Valence])*];
    basis := CartesianProduct(<Basis(spaces[i]) : i in [1..#spaces-1]>);

    MultByMat := function(x, B, i)
      y := x;
      y[i] := y[i]*B;
      return y;
    end function;

    // Checking satisfaction of (x_vav - x_0) * ... * (x_1 - x_0).
    assert forall{c : c in Generators(C) | forall{x : x in basis | forall{i : 
      i in [1..t`Valence] | 
      MultByMat(x, c @ proj[i], i) @ t eq (x @ t)*(c @ proj[#proj])}}};

    printf "  passed!\n";
  end if;

  t`Centroids[2][1] := C;
  return C;
end intrinsic;

intrinsic DerivationAlgebra( t::TenSpcElt ) -> AlgMatLie
{Returns the derivation algebra of the tensor t.}
  if assigned t`Derivations then
    return t`Derivations;
  end if;
  try
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;
  
  if t`Valence eq 3 then
    D := __DerivationsOfBimap( t );
  else
    D := __Derivations( t );
  end if;
  D := __GetSmallerRandomGenerators(D);

  if __SANITY_CHECK then
    printf "Sanity check turned on... (DerivationAlgebra)";
    _, tvs := __TensorOnVectorSpaces(t);
    spaces := __FRAME(tvs);
    dims := [ Dimension(X) : X in spaces ];
    MultiplyByBlock := function(x,B,i)
      x[i] := x[i]*B;
      return x;
    end function;
    for d in Generators(D) do
      blocks := [* ExtractBlock( d, &+(dims[1..i-1] cat [0])+1, &+(dims[1..i-1] cat [0])+1, dims[i], dims[i] ) : i in [1..#dims] *];
      assert forall{ x : x in CartesianProduct( < Basis(X) : X in tvs`Domain > ) |
              &+[ MultiplyByBlock(x,blocks[i],i) @ tvs : i in [1..#dims-1] ] eq (x @ tvs)*blocks[#blocks] };
    end for;
    printf "  DONE!\n";
  end if;

  D`DerivedFrom := < t, [1..t`Valence] >;
  t`Derivations := D;
  return D;
end intrinsic;

intrinsic Nucleus( t::TenSpcElt, a::RngIntElt, b::RngIntElt ) -> AlgMat
{Returns the ab-nucleus of the tensor t.}
  require a ne b : "Integers must be distinct.";
  v := #t`Domain;
  require {a,b} subset {0..v} : "Integers must correspond to Cartesian factors.";
  if t`Cat`Contra then
    require 0 notin {a,b} : "Integers must be positive for cotensors.";
  end if;

  // has it been computed before?
  ind := Index(t`Nuclei[1],{a,b});
  if Type(t`Nuclei[2][ind]) ne RngIntElt then
    return t`Nuclei[2][ind];
  end if;

  x := Maximum([a,b]);
  y := Minimum([a,b]);
  try 
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;

  if t`Valence eq 3 then
    if {a,b} eq {0,1} then
      Nab := __RightNucleusOfBimap(t);
    elif {a,b} eq {0,2} then
      Nab := __LeftNucleusOfBimap(t);
    elif {a,b} eq {1,2} then
      Nab := __MidNucleusOfBimap(t);
    end if;
  else
    // shuffle x,y to v,v-1.
    perm := [0..v];
    if #{x,y,v,v-1} eq 2 then
      perm := [ k : k in [0..v] ];
    elif #{x,y,v,v-1} ne 3 then
      perm[v+1] := x;
      perm[v] := y;
      perm[a+1] := v;
      perm[b+1] := v-1;
    else
      k := Random(Exclude(Exclude({x,y,v-1,v},v-1),v));
      l := Random(Exclude(Exclude({x,y,v-1,v},a),b));
      perm[v+1] := x;
      perm[v] := y;
      perm[k+1] := l;
    end if;
    s := Shuffle( t, perm ); 
    Nab := __21Nucleus(s);
  end if;
  
  if __SANITY_CHECK then
    printf "Sanity check turned on... (Nucleus)";
    _, tvs := __TensorOnVectorSpaces(t);
    spaces := Reverse(__FRAME(tvs));
    MultiplyByBlock := function(x,B,k)
      x[k] := x[k]*B;
      return x;
    end function;
    for z in [Random(Nab) : r in [1..20]] do
      X := ExtractBlock( z, 1, 1, Dimension(spaces[x+1]), Dimension(spaces[x+1]) );
      Y := ExtractBlock( z, Dimension(spaces[x+1])+1, Dimension(spaces[x+1])+1, Dimension(spaces[y+1]), Dimension(spaces[y+1]) );
      if x eq 0 then
        assert forall{ B : B in CartesianProduct( < Basis(X) : X in tvs`Domain > ) | 
          (B @ tvs) * X eq MultiplyByBlock(B,Y,v-y+1) @ tvs };
      elif y eq 0 then
        assert forall{ B : B in CartesianProduct( < Basis(X) : X in tvs`Domain > ) | 
          MultiplyByBlock(B,X,v-x+1) @ tvs eq (B @ tvs) * Y };
      else
        assert forall{ B : B in CartesianProduct( < Basis(X) : X in tvs`Domain > ) | 
          MultiplyByBlock(B,X,v-x+1) @ tvs eq MultiplyByBlock(B,Transpose(Y),v-y+1) @ tvs };
      end if;
    end for;
    printf "  DONE!\n";
  end if;
  Nab`DerivedFrom := < t, [v-x+1,v-y+1] >;
  t`Nuclei[2][ind] := Nab;
  return Nab;
end intrinsic;

intrinsic TensorOverCentroid( t::TenSpcElt ) -> TenSpcElt, Hmtp
{Returns the tensor of t as a tensor over its centroid.}
  if t`Cat`Contra then
    return t;
  end if;
  C := Centroid(t);
  K := BaseRing(C);
  require IsFinite(K) : "Base ring must be finite.";
  n := Nrows(C.1);
  J,S := WedderburnDecomposition(C);
  require IsCommutative(S) : "Centroid is not a commutative ring.";
  if Generators(S) eq { Generic(S)!1 } then
    return t,_;
  end if;
  isit,X := __IsCyclic(S);
  require isit : "Centroid is not a commutative local ring.";
  
  D := t`Domain;
  C := t`Codomain;
  dims := [ Dimension(X) : X in D ] cat [ Dimension(C) ];
  blocks := [* ExtractBlock( X, &+(dims[1..i-1] cat [0]) + 1, &+(dims[1..i-1] cat [0]) + 1, dims[i], dims[i] ) : i in [1..#dims] *];
  Exts := [* ext< K | MinimalPolynomial(blocks[i]) > : i in [1..#dims] *];
  E := GF( #Exts[1] );
  phi := [* *]; 
  phi_inv := [* *];
  for i in [1..#Exts] do
    f,g := __GetFieldHom( Exts[i], E );
    Append(~phi,f);
    Append(~phi_inv,g);
  end for;
  e := Degree( E, K );
  Y := [* &+[ Eltseq(E.1@phi_inv[j])[i]*blocks[j]^(i-1) : i in [1..e] ] : j in [1..#phi] *];
  
  Spaces := __FRAME(t);
  InvSubs := [* [ [ Spaces[i].1*Y[i]^j : j in [0..e-1] ] ] : i in [1..#Spaces] *]; // cent-invariant subspaces
  // loop through the spaces and get the rest of the cent-invariant subspaces
  for i in [1..#Spaces] do
    notdone := true;
    while notdone do
      U := &+([ sub< Spaces[i] | B > : B in InvSubs[i] ]);
      Q,pi := Spaces[i]/U;
      if Dimension(Q) eq 0 then
        notdone := false;
      else
        S := [ (Q.1@@pi)*Y[i]^j : j in [0..e-1] ];
        Append(~InvSubs[i],S);
      end if;
    end while;
  end for;
  Bases := [* &cat[ S : S in InvSubs[i] ] : i in [1..#Spaces] *];
  VS := [* VectorSpaceWithBasis( B ) : B in Bases *];

  dom := [* VectorSpace( E, dims[i] div e ) : i in [1..#dims-1] *];
  cod := VectorSpace( E, dims[#dims] div e );

  ToNewSpace := function(x,i)
    c := Coordinates(VS[i],VS[i]!x);
    vec := [ E!(c[(j-1)*e+1..j*e]) : j in [1..dims[i] div e] ]; 
    return vec;
  end function;

  ToOldSpace := function(y,i)
    c := Eltseq(y);
    vec := &cat[ Eltseq(c[j]) : j in [1..#c] ];
    vec := &+[ vec[j]*Bases[i][j] : j in [1..#Bases[i]] ];
    return vec;
  end function;

  Maps := [* map< D[i] -> dom[i] | x :-> dom[i]!ToNewSpace(x,i), y :-> D[i]!ToOldSpace(y,i) > : i in [1..#D] *];
  Maps cat:= [* map< C -> cod | x :-> cod!ToNewSpace(x,#VS), y :-> C!ToOldSpace(y,#VS) > *];

  F := function(x)
    return (< x[i] @@ Maps[i] : i in [1..#x] > @ t) @ Maps[#Maps];
  end function;

  s := __GetTensor( dom, cod, F : Cat := t`Cat );
  H := __GetHomotopism( t, s, Maps : Cat := HomotopismCategory(t`Valence) );
  if assigned t`Coerce then
    s`Coerce := [* t`Coerce[i] * Maps[i] : i in [1..#t`Coerce] *];
  end if;

  if __SANITY_CHECK then
    printf "Sanity check turned on... (TensorOverCentroid)";
    assert forall{ x : x in CartesianProduct( < Basis( X ) : X in t`Domain > ) |
           (< x[i] @ Maps[i] : i in [1..#x] > @ s) eq ((x @ t) @ Maps[#Maps]) };
    // verifies if multilinear.
    D := Domain(s);
    K := BaseRing(s);
    U := { k : k in K | k ne 0 };
    for i in [1..10] do
      C := [ Random(U) : i in [1..#D] ];
      x := < Random(d) : d in D >;
      y := < Random(d) : d in D >;
      k := &*C;
      z := < C[i]*x[i] + y[i] : i in [1..#x] >;
      for i in [1..#D] do
        u := z;
        v := z;
        u[i] := x[i];
        v[i] := y[i];
        assert z@s eq C[i]*(u@s)+(v@s);
      end for;
    end for;
    printf "  DONE!\n";
  end if;

  return s,H;
end intrinsic;

// ==============================================================================
//                              Optimized for bimaps
// ==============================================================================
intrinsic AdjointAlgebra( t::TenSpcElt ) -> AlgMat
{Returns the adjoint *-algebra of the 2-tensor t.}
  require t`Valence eq 3 : "Tensor must have valence 3.";
  if assigned t`Bimap`Adjoint then
    return t`Bimap`Adjoint;
  end if;
  try 
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;
  
  S := SystemOfForms(t);
  A := AdjointAlgebra(S);
  A`DerivedFrom := < t, [1,2] >;
  t`Bimap`Adjoint := A;
  return A;
end intrinsic;

intrinsic LeftNucleus( t::TenSpcElt ) -> AlgMat
{Returns the left nucleus of the 2-tensor t.}
  require t`Valence eq 3 : "Tensor must have valence 3.";
  ind := Index(t`Nuclei[1], {0,2});
  if Type(t`Nuclei[2][ind]) ne RngIntElt then
    return t`Nuclei[2][ind];
  end if;
  try 
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;
  L := __LeftNucleusOfBimap(t);

  if __SANITY_CHECK then
    printf "Sanity check turned on... (LeftScalars)";
    S := SystemOfForms(t);
    for l in Generators(L) do
      X := ExtractBlock(l,1,1,Nrows(S[1]),Nrows(S[1]));
      Z := ExtractBlock(l,Nrows(S[1])+1,Nrows(S[1])+1,#S,#S);
      assert [ Transpose(X)*S[i] : i in [1..#S] ] eq [ &+[ Z[i][j]*S[j] : j in [1..#S] ] : i in [1..#S] ];
    end for;
    printf "  DONE!\n";
  end if;
  L`DerivedFrom := < t, [1,3] >;
  t`Nuclei[2][ind] := L;
  return L;
end intrinsic;

intrinsic MidNucleus( t::TenSpcElt ) -> AlgMat
{Returns the mid nucleus of the 2-tensor t.}
  require t`Valence eq 3 : "Tensor must have valence 3.";
  return Nucleus(t,2,1);
end intrinsic;

intrinsic RightNucleus( t::TenSpcElt ) -> AlgMat
{Returns the right nucleus of the 2-tensor t.}
  require t`Valence eq 3 : "Tensor must have valence 3.";
  ind := Index(t`Nuclei[1], {0,1});
  if Type(t`Nuclei[2][ind]) ne RngIntElt then
    return t`Nuclei[2][ind];
  end if;
  try 
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;
  R := __RightNucleusOfBimap(t);

  if __SANITY_CHECK then
    printf "Sanity check turned on... (RightScalars)";
    S := SystemOfForms(t);
    for r in Generators(R) do
      Y := ExtractBlock(r,1,1,Ncols(S[1]),Ncols(S[1]));
      Z := ExtractBlock(r,Ncols(S[1])+1,Ncols(S[1])+1,#S,#S);
      assert [ S[i]*Transpose(Y) : i in [1..#S] ] eq [ &+[ S[j]*Z[j][i] : j in [1..#S] ] : i in [1..#S] ];
    end for;
    printf "  DONE!\n";
  end if;
  R`DerivedFrom := < t, [2,3] >;
  t`Nuclei[2][ind] := R;
  return R;
end intrinsic;

// ==============================================================================
//                           Polynomial-based invariants
// ==============================================================================
intrinsic Discriminant( t::TenSpcElt ) -> RngMPolElt
{Returns the (generalized) discriminant of the 2-tensor t.}
  require t`Valence eq 3 : "Only defined for tensors of valence 3.";
  K := BaseRing(t);
  require Type(K) ne BoolElt : "Tensor must have a base ring.";
  require Dimension(t`Domain[1]) eq Dimension(t`Domain[2]) : "Discriminant not defined for this tensor.";
  C := t`Codomain;
  n := Dimension(C);
  R := PolynomialRing(K,n);
  try
    S := SystemOfForms(t);
  catch err
    error "Cannot compute structure constants.";
  end try;
  MA := MatrixAlgebra(K,Nrows(S[1]));
  return Determinant( &+[ (MA!S[i])*R.i : i in [1..n] ] );
end intrinsic;

intrinsic Pfaffian( t::TenSpcElt ) -> RngMPolElt
{Returns the (generalized) Pfaffian of the alternating bimap.}
  require t`Valence eq 3 : "Only defined for tensors of valence 3.";
  require IsAlternating(t) : "Tensor must be alternating.";
  try
    disc := Discriminant(t);
  catch err
    error "Cannot compute the discriminant of the bimap."; 
  end try;
  if disc ne Parent(disc)!0 then
    factors := Factorisation(disc);
    assert forall{ f : f in factors | IsEven(f[2]) };
    return &*[ f[1]^(f[2] div 2) : f in factors ];
  end if;
  return Parent(disc)!0;
end intrinsic;
