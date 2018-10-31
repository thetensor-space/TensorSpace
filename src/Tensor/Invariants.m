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
import "../GlobalVars.m" : __SANITY_CHECK, __FRAME;
import "../Types.m" : __RF_DERIVED_FROM;
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
  newBasis := [[*x : x in b*] : b in basis];
  for S in toFuse do
    T := S diff {Max(S)};
    for t in T do
      if t in coords then
        i := Index(coords, t);
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
  return [<x : x in b> : b in newBasis];
end function;


/* 
  Given: t (TenSpcElt), A ({RngIntElt} a subset of [vav])
  Return: [Tup] (Tup are contained in Prod_a End(U_a))

  + Note that if |A| = 2, then this is actually a nucleus computation. 

  + We leave it to the function calling this to organize and find appropriate 
    representations.

  Complexity: If D is the product of dimensions in dims, and S is the sum of 
    squares of the dimensions supported by A, then this algorithm constructs a 
    basis for the kernel of a K-matrix with (|A|-1)*D rows and S columns.
*/
__A_Centroid := function(seq, dims, A)
  // Initial setup.
  a := Minimum(A);
  B := A diff {a};
  d := &*(dims);
  K := Parent(seq[1]);
  v := #dims;
  d_a := dims[v-a];
  M := ZeroMatrix(K, #B*d, &+[dims[v-x]^2 : x in A]);
  I := IdentityMatrix(K, d_a);
  r_anchor := Ncols(M) - d_a^2 + 1;
  
  // Construct the appropriate matrix. 
  // We place the a block on the right-most side of M.
  row := 1;
  col := 1;
  while #B gt 0 do
    b := Maximum(B);
    B := B diff {b};
    d_b := dims[v-b];

    Mats := __GetForms(seq, dims, b, a : op := true);
    LeftBlocks := [Matrix(K, [Eltseq(Mats[k][i]) : k in [1..#Mats]]) : 
      i in [1..d_a]];
    Mats := [Transpose(X) : X in Mats];
    RightBlock := -Matrix(K, &cat[[Eltseq(Mats[k][j]) : k in [1..#Mats]] : 
      j in [1..d_b]]);
    delete Mats;

    // Building the matrix strip for the equation x_a = x_b.
    // The blocks corresponding to the x_a part.
    InsertBlock(~M, KroneckerProduct(I, RightBlock), row, r_anchor);
    delete RightBlock;

    // The blocks corresponding to the x_b part. 
    for i in [1..#LeftBlocks] do
      InsertBlock(~M, KroneckerProduct(IdentityMatrix(K, d_b), LeftBlocks[i]), 
        row, col);
      row +:= d_b*Nrows(LeftBlocks[i]);
    end for;
    delete LeftBlocks;
    
    col +:= d_b^2;
  end while;

  // Solve the linear equations
  N := NullspaceOfTranspose(M);
  delete M;

  // Interpret the nullspace as matrices
  basis := [];
  for b in Basis(N) do
    T := <>;
    vec := Eltseq(b);
    for a in Reverse(Sort([a : a in A])) do
      MA := MatrixAlgebra(K, dims[v-a]);
      Append(~T, MA!vec[1..dims[v-a]^2]);
      vec := vec[dims[v-a]^2+1..#vec];
    end for;
    Append(~basis, T);
  end for;

  // We want to return everything to End(U_i) (in particular, no op).
  // If 0 is in A, then we need to transpose the matrices.
  if 0 in A then
    for i in [1..#basis] do
      basis[i][#basis[i]] := Transpose(basis[i][#basis[i]]);
    end for;
  end if;

  return basis;
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
  B := Basis(N);
  if Dimension(N) eq 0 then
    B := [N!0];
  end if;
  basis := [__VectorToBlocks(b, dims cat [d]) : b in B];
  return __ReduceByFuse(basis, RepeatPartition(TensorCategory(t)), \
    Reverse([0..#Domain(t)]));
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
  if #basis eq 0 then
    basis := [<ZeroMatrix(K, a, a), ZeroMatrix(K, b, b), ZeroMatrix(K, c, c)>];
  end if;
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
  v := t`Valence;
  require a ge 1 : "Argument must be a positive integer.";
  require a lt v : "Argument exceeds coordinates in the domain.";
  require ISA(Type(BaseRing(t)), Fld) : "Radicals only implemented for tensors over fields.";
  if Type(t`Radicals[v - a]) ne RngIntElt then
    return t`Radicals[v - a];
  end if;

  try 
    F := Foliation(t, a);
  catch err
    error "Cannot compute structure constants.";
  end try;

  D := t`Domain[v - a];
  B := Basis(D);
  V := VectorSpace(BaseRing(t), #B);
  vprint eMAGma, 1 : "Solving linear system " cat IntegerToString(Nrows(F)) \
    cat " by " cat IntegerToString(Ncols(F));
  R := Nullspace(F);
  
  t`Radicals[v - a] := R;
  return R;
end intrinsic;

intrinsic Coradical( t::TenSpcElt ) -> ModTupRng, Map
{Returns the coradical of t.}
  if Type(t`Radicals[t`Valence]) ne RngIntElt then
    return t`Radicals[t`Valence][1],t`Radicals[t`Valence][2];
  end if;
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
  return Centroid(t, {0..Valence(t)-1});
end intrinsic;

intrinsic Centroid( t::TenSpcElt, A::{RngIntElt} ) -> AlgMat
{Returns the A-centroid of the tensor t.}
  // Check A makes sense.
  require A subset {0..Valence(t)-1} : "Unknown tensor coordinates.";
  require #A ge 2 : "Must be at least two coordinates.";
  if #A eq 2 then
    return Nucleus(t, Maximum(A), Minimum(A));
  end if;

  // Check if the centroid has been computed before.
  ind := Index(t`Centroids[1], A);
  if Type(t`Centroids[2][ind]) ne RngIntElt then
    return t`Centroids[2][ind];
  end if;
   
  // Make sure we can obtain the structure constants. 
  try
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;

  basis := __A_Centroid(Eltseq(t), [Dimension(X) : X in Frame(t)], A);
  
  // Take the block-basis and construct the corresponding matrix algebra.
  basis := [DiagonalJoin(T) : T in basis];
  MA := MatrixAlgebra(BaseRing(t), Nrows(basis[1]));
  C := sub< MA | basis >;
  C := __GetSmallerRandomGenerators(C);
  C`DerivedFrom := rec< __RF_DERIVED_FROM | 
    Tensor := t, Indices := [Valence(t) - a : a in A], Fused := false >; // COME BACK AND INCLUDE FUSE

  // Sanity check
  if __SANITY_CHECK then
    // Preliminaries  
    printf "Running sanity check (Centroid)\n";
    proj := [*Induce(C, a) : a in Reverse([0..t`Valence-1])*];
    basis := CartesianProduct(<Basis(X) : X in Domain(t)>);

    // A function to only change one coordinate.
    MultByMat := function(x, B, i)
      y := x;
      y[i] := y[i]*B;
      return y;
    end function;

    // Checking satisfaction of (x_vav - x_0) meet ... meet (x_1 - x_0).
    assert forall{c : c in Generators(C) | forall{x : x in basis | forall{i : \
      i in [1..t`Valence-1] | \
      MultByMat(x, c @ proj[i], i) @ t eq (x @ t)*(c @ proj[#proj]) \
      }}};
  end if;

  // Save and return.
  t`Centroids[2][ind] := C;
  return C;
end intrinsic;

intrinsic DerivationAlgebra( t::TenSpcElt ) -> AlgMatLie
{Returns the derivation algebra of the tensor t.}
  // Check if the derivations have been computed before.
  if assigned t`Derivations then
    return t`Derivations;
  end if;

  // Make sure we can obtain the structure constants. 
  try
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;
  
  // Determine which algorithm to use. 
  if t`Valence eq 3 then
    basis := __DerivationsOfBimap( t );
  else
    basis := __Derivations( t );
  end if;

  // Take the block-basis and construct the corresponding matrix Lie algebra.
  basis := [DiagonalJoin(T) : T in basis];
  MLA := MatrixLieAlgebra(BaseRing(basis[1]), Nrows(basis[1]));
  D := sub< MLA | basis >;
  D := __GetSmallerRandomGenerators(D);
  D`DerivedFrom := rec< __RF_DERIVED_FROM | 
    Tensor := t, Indices := [1..t`Valence], Fused := true >;


  // Sanity check
  if __SANITY_CHECK then
    // Preliminaries
    printf "Running sanity check (DerivationAlgebra)\n";
    proj := [*Induce(D, a) : a in Reverse([0..t`Valence-1])*];
    basis := CartesianProduct(<Basis(X) : X in Domain(t)>);

    // A function to only change one coordinate.
    MultByMat := function(x, B, i)
      y := x;
      y[i] := y[i]*B;
      return y;
    end function;

    // Checking satisfaction of (x_vav + ... + x_1 - x_0).
    assert forall{d : d in Generators(D) | forall{x : x in basis | \
      &+[MultByMat(x, d @ proj[i], i) @ t : i in [1..#proj-1]] eq \
      (x @ t)*(d @ proj[#proj]) \
      }};
  end if;

  // Save and return.
  t`Derivations := D;
  return D;
end intrinsic;

intrinsic Nucleus( t::TenSpcElt, a::RngIntElt, b::RngIntElt ) -> AlgMat
{Returns the ab-nucleus of the tensor t.}
  // Make sure {a,b} make sense.
  require a ne b : "Integers must be distinct.";
  v := Valence(t);
  require {a,b} subset {0..v-1} : \
    "Integers must correspond to Cartesian factors.";
  if t`Cat`Contra then
    require 0 notin {a,b} : "Integers must be positive for cotensors.";
  end if;

  // Check if it has been computed before.
  ind := Index(t`Nuclei[1], {a,b});
  if Type(t`Nuclei[2][ind]) ne RngIntElt then
    return t`Nuclei[2][ind];
  end if;

  // Make sure we can obtain the structure constants. 
  try 
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;

  T := __A_Centroid(Eltseq(t), [Dimension(X) : X in Frame(t)], {a, b});

  // Get the right representation.
  if 0 notin {a, b} then
    for i in [1..#T] do
      T[i][2] := Transpose(T[i][2]);
    end for;
  end if;

  // Put everything together.
  basis := [DiagonalJoin(t[1], t[2]) : t in T];
  MA := MatrixAlgebra(BaseRing(basis[1]), Nrows(basis[1]));
  Nuke := sub< MA | basis >;
  Nuke := __GetSmallerRandomGenerators(Nuke);
  max := Maximum([a, b]);
  min := Minimum([a, b]);
  Nuke`DerivedFrom := rec< __RF_DERIVED_FROM | 
    Tensor := t, Indices := [v - max, v - min], Fused := false >;

  return Nuke;
end intrinsic;

intrinsic TensorOverCentroid( t::TenSpcElt ) -> TenSpcElt, Hmtp
{Returns the tensor of t as a tensor over its centroid.}
  // If co-tensor, then stop as t is a form.
  if t`Cat`Contra then
    return t;
  end if;

  // Compute centroid and make sure it is suitable.
  Cent := Centroid(t);
  K := BaseRing(Cent);
  require IsFinite(K) : "Base ring must be finite."; // __IsCyclic needs finite.
  n := Nrows(Cent.1);
  J, S := WedderburnDecomposition(Cent);
  require IsCommutative(S) : "Centroid is not a commutative ring.";
  if Generators(S) eq {Generic(S)!1} then
    // It is already written over its centroid.
    return t, _;
  end if;
  isit, X := __IsCyclic(S);
  require isit : "Centroid is not a commutative local ring.";
  
  // Construct field extensions and one "standard" field ext (given by 'GF').
  D := t`Domain;
  C := t`Codomain;
  dims := [Dimension(X) : X in D] cat [Dimension(C)];
  proj := [*Induce(Cent, a) : a in Reverse([0..#D])*];
  blocks := [*X @ proj[i] : i in [1..#dims]*];
  Exts := [*ext< K | MinimalPolynomial(blocks[i]) > : i in [1..#dims]*];
  E := GF(#Exts[1]); // standard extension

  // Construct isomorphisms to and from each Exts[i] and E.
  phi := [**]; 
  phi_inv := [**];
  for i in [1..#Exts] do
    f, g := __GetFieldHom(Exts[i], E);
    Append(~phi, f);
    Append(~phi_inv, g);
  end for;
  e := Degree(E, K);
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
    printf "Running sanity check (TensorOverCentroid)\n";
    basis := CartesianProduct(<Basis(X) : X in t`Domain>);

    // First verify that the maps produce an actual homotopism from t to s.
    assert forall{x : x in basis | 
      <x[i] @ Maps[i] : i in [1..#x]> @ s eq (x @ t) @ Maps[#Maps]
      };

    // Now verify that s is E-multilinear.
    D := Domain(s);
    E := BaseRing(s);
    U, phi := UnitGroup(E);
    for i in [1..10] do
      C := [Random(U) @ phi : i in [1..#D]];
      x := <Random(d) : d in D>;
      y := <Random(d) : d in D>;
      k := &*C;
      z := <C[i]*x[i] + y[i] : i in [1..#x]>;
      for i in [1..#D] do
        u := z;
        v := z;
        u[i] := x[i];
        v[i] := y[i];
        assert z @ s eq C[i]*(u @ s) + (v @ s);
      end for;
    end for;
  end if;

  return s, H;
end intrinsic;

// ==============================================================================
//                              Optimized for bimaps
// ==============================================================================
intrinsic AdjointAlgebra( t::TenSpcElt ) -> AlgMat
{Returns the adjoint *-algebra of the 3-tensor t.}
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
  A`DerivedFrom := rec< __RF_DERIVED_FROM | 
    Tensor := t, Indices := [1], Fused := false >;
  t`Bimap`Adjoint := A;
  return A;
end intrinsic;

intrinsic LeftNucleus( t::TenSpcElt : op := false ) -> AlgMat
{Returns the left nucleus of the 3-tensor t.}
  require t`Valence eq 3 : "Tensor must have valence 3.";
  Nuke := Nucleus(t, 2, 0);
  if op then
    N := sub< Generic(Nuke) | [Transpose(X) : X in Generators(Nuke)] >;
    N`DerivedFrom := Nuke`DerivedFrom;
    t`Nuclei[2][2] := N;
    return N;
  else
    return Nuke;
  end if;
end intrinsic;

intrinsic MidNucleus( t::TenSpcElt ) -> AlgMat
{Returns the mid nucleus of the 3-tensor t.}
  require t`Valence eq 3 : "Tensor must have valence 3.";
  return Nucleus(t, 2, 1);
end intrinsic;

intrinsic RightNucleus( t::TenSpcElt ) -> AlgMat
{Returns the right nucleus of the 3-tensor t.}
  require t`Valence eq 3 : "Tensor must have valence 3.";
  return Nucleus(t, 1, 0);
end intrinsic;

// ==============================================================================
//                           Polynomial-based invariants
// ==============================================================================
intrinsic Discriminant( t::TenSpcElt ) -> RngMPolElt
{Returns the (generalized) discriminant of the 3-tensor t.}
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
{Returns the (generalized) Pfaffian of the alternating 3-tensor.}
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
