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
import "TensorData.m" : __GetForms, __GetSlice;
import "../TensorCategory/Hom.m" : __GetHomotopism;
import "../GlobalVars.m" : __SANITY_CHECK, __FRAME;
import "../Types.m" : __RF_DERIVED_FROM;
import "../Util/ConjugateCyclic.m" : __IsCyclic;

// A function to remove superfluous blocks for fused coordinates. 
/*
  Given a basis as a tuple of blocks, partition as a set of subsets of {0..v}, 
  and coords as a sequence aligned with basis.
*/
__ReduceByFuse := function(basis, partition, coords)
  K := BaseRing(basis[1][1]);
  toFuse := [S meet Set(coords) : S in partition | #(S meet Set(coords)) gt 1];
  newBasis := [[*x : x in b*] : b in basis];
  newCoords := {s : s in S meet Set(coords), S in partition | #S eq 1};

  for S in toFuse do
    T := S diff {Max(S)};
    Include(~newCoords, Max(S));
    for t in T do
      i := Index(coords, t);
      for j in [1..#newBasis] do
        newBasis[j][i] := IdentityMatrix(K, 0);
      end for;
    end for;
  end for;

  return [<x : x in b> : b in newBasis], newCoords;
end function;


/*
  Given: K (Fld), dims ([RngIntElt]), repeats ({SetEnum}), A ({RngIntElt}).
  Returns: A matrix with I and -I strategically placed so that the corresponding
    linear system will equate the operators supported on repeats, relative to A.

    This matrix should be vertically joined to ensure that coordinates that are
  fused are equal. 
*/  
__FusionBlock := function(K, dims, repeats, A)
  // Setup.
  v := #dims;
  S := &+[dims[v-a]^2 : a in A];
  R := {X meet A : X in repeats | #(X meet A) gt 1};
  n := &+([(#r-1)*dims[v - Minimum(r)]^2 : r in R] cat [0]);
  
  M := ZeroMatrix(K, n, S);
  // If no repeats relative to A, we are done. 
  // Returns a (0 x S)-matrix to prevent issues with VerticalJoin.
  if n eq 0 then return M; end if;
  
  // Run through the repeats.
  row := 1;
  for r in R do
    // We fix a for this particular r, and compare everything to this.
    a := Minimum(r);
    B := r diff {a};
    if a ne 0 then
      I := IdentityMatrix(K, dims[v-a]^2);
    else
      temp := Matrix(Integers(), dims[v], dims[v], [1..dims[v]^2]);
      temp := Eltseq(Transpose(temp));
      I := PermutationMatrix(K, temp);
    end if;
    rcol := S - &+[dims[v-a+i]^2 : i in [0..a] | a-i in A] + 1;
    // Run though the set r - a.
    while #B gt 0 do
      b := Minimum(B);
      B diff:= {b};
      lcol := S - &+[dims[v-b+i]^2 : i in [0..b] | b-i in A] + 1;

      // Place the blocks.      
      InsertBlock(~M, IdentityMatrix(K, dims[v-a]^2), row, lcol);
      InsertBlock(~M, -I, row, rcol);

      row +:= dims[v-a]^2;
    end while;
  end for;

  return M;
end function;

/* 
  Given: t (TenSpcElt), A ({RngIntElt} a subset of [vav])
  Return: [Tup] (Tup are contained in Prod_a End(U_a))

  These are the operators that satisfy 
      \bigcap_{b \in A - \{a\}} (x_a - x_b).

  + Note that if |A| = 2, then this is actually a nucleus computation. 

  + We leave it to the function calling this to organize and find appropriate 
    representations.

  Complexity: If D is the product of dimensions in dims, and S is the sum of 
    squares of the dimensions supported by A, then this algorithm constructs a 
    basis for the kernel of a K-matrix with (|A|-1)*D rows and S columns.
*/
__A_Centroid := function(seq, dims, A : repeats := {})
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
  
  vprintf eMAGma, 1 : "Constructing a %o by %o matrix over %o.\n", Ncols(M), 
    Nrows(M), K;
  
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

  // Check repeats.
  if #repeats ne 0 then
    vprint eMAGma, 1 : "Adding in fusion data.";
    R := __FusionBlock(K, dims, repeats, A);
    M := VerticalJoin(R, M);
  end if;

  // Solve the linear equations.
  vprintf eMAGma, 1 : "Computing the nullspace of a %o by %o matrix.\n", Ncols(M),
    Nrows(M);
  N := NullspaceOfTranspose(M);
  delete M;

  // Interpret the nullspace as matrices.
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

/*
  This is essentially Transpose(Foliation(t, a)), but it splits up the matrix 
  into k equal pieces.
*/
__Coordinate_Spread := function(seq, dims, a, k)
  v := #dims;
  d_a := dims[v-a];
  dims_a := dims;
  dims_a[v-a] := 1;
  CP := CartesianProduct(< [1..d] : d in dims_a >);
  rows := [];
  for c in CP do
    grid := [{x} : x in c];
    grid[v-a] := {1..d_a};
    Append(~rows, __GetSlice(seq, dims, grid));
  end for;
  d := &*(dims_a) div k;
  if a eq 0 then 
    ep := -1; 
  else 
    ep := 1;
  end if;
  Mats := [ep*Matrix(rows[(i-1)*d+1..i*d]) : i in [1..k]];
  return Mats;
end function;


/* 
  Given: t (TenSpcElt), A ({RngIntElt} a subset of [vav])
  Return: [Tup] (Tup are contained in Prod_a End(U_a))

  These are the operators that satisfy
      (\sum_{a \in A} x_a)            if 0 not in A,
      (\sum_{a \in A-0} x_a - x_0)    if 0 in A.

  + We leave it to the function calling this to organize and find appropriate 
    representations.

  Complexity: If D is the product of dimensions in dims, and S is the sum of 
    squares of the dimensions supported by A, then this algorithm constructs a 
    basis for the kernel of a K-matrix with D rows and S columns.
*/

__A_Derivations := function(seq, dims, A, repeats)
  // Initial setup.
  d := &*(dims);
  K := Parent(seq[1]);
  v := #dims;
  s := &+[dims[v-x]^2 : x in A];
  M := ZeroMatrix(K, d, s);
  vprintf eMAGma, 1 : "Construting a %o by %o matrix over %o.\n", Ncols(M), 
    Nrows(M), K;

  // Construct the appropriate matrix.
  // We work from right to left.
  B := A;
  col := s+1;
  depth := d;
  while #B gt 0 do
    row := 1;
    a := Minimum(B);
    B diff:= {a};
    d_a := dims[v-a];
    col -:= d_a^2;
    depth div:= d_a;

    // A chopped up foliation.
    Mats := __Coordinate_Spread(seq, dims, a, depth);

    // Add the matrices to our big matrix.
    I := IdentityMatrix(K, d_a);
    r := d_a * Nrows(Mats[1]);
    for X in Mats do
      InsertBlock(~M, KroneckerProduct(I, X), row, col);
      row +:= r;
    end for;

  end while;

  // Get the repeats block.
  vprint eMAGma, 1 : "Adding in fusion data.";
  M := VerticalJoin(__FusionBlock(K, dims, repeats, A), M);
  
  // Solve the linear system.
  vprintf eMAGma, 1 : "Computing the nullspace of a %o by %o matrix.\n", 
    Ncols(M), Nrows(M);
  N := NullspaceOfTranspose(M);

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
  // If 0 is in A, then we need to negate and transpose the matrices.
  if 0 in A then
    for i in [1..#basis] do
      basis[i][#basis[i]] := Transpose(basis[i][#basis[i]]);
    end for;
  end if;

  return basis;
end function;


/* 
  Kantor's Lemma as described in Brooksbank, Wilson, "The module isomorphism 
    problem reconsidered," 2015.
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

// Given a tensor t, a set of coords A, a boolean F, a function ALG, a seq of 
// tuples B, and a string obj return algebra derived from the tensor. 
__MakeAlgebra := function(t, A, F, ALG, B, obj);
  coords := Reverse(Sort([a : a in A]));
  if F then
    B, A_rep := __ReduceByFuse(B, t`Cat`Repeats, coords);
  else
    A_rep := A;
  end if;
  basis := [DiagonalJoin(T) : T in B];
  MA := ALG(BaseRing(t), Nrows(basis[1]));
  Operators := sub< MA | basis >;
  Operators := __GetSmallerRandomGenerators(Operators);
  Operators`DerivedFrom := rec< __RF_DERIVED_FROM | Tensor := t, Coords := A, 
    Fused := F, Object := obj, RepCoords := A_rep >; 
  return Operators, B;
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
  // Check that A makes sense.
  require A subset {0..Valence(t)-1} : "Unknown tensor coordinates.";
  require #A ge 2 : "Must be at least two coordinates.";
  if t`Cat`Contra then
    require 0 notin A : "Integers must be positive for cotensors.";
  end if;
  
  // |A| = 2 case.
  if #A eq 2 then
    return Nucleus(t, Maximum(A), Minimum(A));
  end if;

  // Check if the centroid has been computed before.
  ind := Index(t`Centroids[1], A);
  if Type(t`Centroids[2][ind]) ne RngIntElt then
    // If it has been, return it as an algebra. 
    C := __MakeAlgebra(t, A, true, MatrixAlgebra, t`Centroids[2][ind], 
      "Centroid");
    return C;
  end if;
   
  // Now it hasn't been computed before, and we need to compute something.
  // Make sure we can obtain the structure constants. 
  try
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;

  basis := __A_Centroid(Eltseq(t), [Dimension(X) : X in Frame(t)], A : 
    repeats := t`Cat`Repeats);

  // Save the algebra
  C, basis := __MakeAlgebra(t, A, true, MatrixAlgebra, basis, "Centroid");
  t`Centroids[2][ind] := basis;

  // Sanity check
  if __SANITY_CHECK then
    // Preliminaries  
    printf "Running sanity check (Centroid)\n";
    inds := [*a : a in A*];
    proj := [*Induce(C, a) : a in A*];
    dom_basis := CartesianProduct(<Basis(X) : X in Domain(t)>);
    m := Minimum(A);

    // A function to only change one coordinate.
    MultByMat := function(x, B, a)
      y := x;
      y[Valence(t) - a] := y[Valence(t) - a]*B;
      return y;
    end function;

    // Checking satisfaction of (x_a - x_m), for all a in A - {m}.
    if m eq 0 then 
      assert forall{c : c in Generators(C) | forall{x : x in dom_basis | forall{a : \
        a in A diff {m} | \
        MultByMat(x, c @ proj[Index(inds, a)], a) @ t eq (x @ t)*(c @ proj[Index(inds, m)]) \
        }}};
    else
      assert forall{c : c in Generators(C) | forall{x : x in dom_basis | forall{a : \
        a in A diff {m} | \
        MultByMat(x, c @ proj[Index(inds, a)], a) @ t eq \
        MultByMat(x, c @ proj[Index(inds, m)], m) @ t
        }}};
    end if;
  end if;

  return C;
end intrinsic;

intrinsic DerivationAlgebra( t::TenSpcElt ) -> AlgMatLie
{Returns the derivation algebra of the tensor t.}
  return DerivationAlgebra(t, {0..Valence(t)-1});
end intrinsic;

intrinsic DerivationAlgebra( t::TenSpcElt, A::{RngIntElt} ) -> AlgMatLie
{Returns the A-derivation algebra of the tensor t.}
  // Make sure A makes sense.
  require A subset {0..Valence(t)-1} : "Unknown coordinates.";
  require #A gt 1 : "Set must contain at least two coordinates.";
  if t`Cat`Contra then
    require 0 notin A : "Integers must be positive for cotensors.";
  end if;

  // Make sure we can obtain the structure constants. 
  try
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;

  // Deal with the #A = 2 case.
  if #A eq 2 then
    // Compute the nucleus. 
    _ := Nucleus(t, Maximum(A), Minimum(A));
    ind := Index(t`Nuclei[1], A);
    basis := t`Nuclei[2][ind];
    // If 0 is not in A, then op and negate it. Effectively turning x_a - x_b to
    // the correct derivation polynomial.
    if 0 notin A then
      basis := [<N[1], -Transpose(N[2])> : N in basis];
    end if;
    D := __MakeAlgebra(t, A, true, MatrixLieAlgebra, basis, "Derivation");
    return D;
  end if;

  // Check if the derivations have been computed before.
  ind := Index(t`Derivations[1], A);
  if Type(t`Derivations[2][ind]) ne RngIntElt then
    D := __MakeAlgebra(t, A, true, MatrixLieAlgebra, t`Derivations[2][ind], 
      "Derivation");
    return D;
  end if; 

  // Get the derivations
  basis := __A_Derivations(Eltseq(t), [Dimension(X) : X in Frame(t)], A,
    t`Cat`Repeats);

  // Save the algebra
  D, basis := __MakeAlgebra(t, A, true, MatrixLieAlgebra, basis, "Derivation");
  t`Derivations[2][ind] := basis;

  // Sanity check
  if __SANITY_CHECK then
    // Preliminaries  
    printf "Running sanity check (DerivationAlgebra)\n";
    inds := [*a : a in A*];
    proj := [*Induce(D, a) : a in A*];
    dom_basis := CartesianProduct(<Basis(X) : X in Domain(t)>);
    m := Minimum(A);

    // A function to only change one coordinate.
    MultByMat := function(x, B, a)
      y := x;
      y[Valence(t) - a] := y[Valence(t) - a]*Matrix(B);
      return y;
    end function;

    // Checking satisfaction of the derivation polynomial.
    if m eq 0 then
      assert forall{del : del in Generators(D) | forall{x : x in dom_basis | 
        &+[MultByMat(x, del @ proj[Index(inds, a)], a) @ t : a in A diff {m}] eq
          (x @ t)*Matrix(del @ proj[Index(inds, m)]) \
        }};
    else
      assert forall{del : del in Generators(D) | forall{x : x in dom_basis | 
        &+[MultByMat(x, del @ proj[Index(inds, a)], a) @ t : a in A diff {m}] +
          MultByMat(x, del @ proj[Index(inds, m)], m) @ t eq (t`Codomain)!0 \
        }};
    end if;
  end if;

  return D;
end intrinsic;

intrinsic Nucleus( t::TenSpcElt, A::{RngIntElt} ) -> AlgMat
{Returns the A-nucleus of the tensor t, for |A| = 2.}
  require #A eq 2 : "Set must contain exactly two coordinates.";
  return Nucleus(t, Maximum(A), Minimum(A));
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
  ind := Index(t`Nuclei[1], {a, b});
  if Type(t`Nuclei[2][ind]) ne RngIntElt then
    Nuke := __MakeAlgebra(t, {a, b}, false, MatrixAlgebra, t`Nuclei[2][ind], 
      "Nucleus");
    return Nuke;
  end if;

  // Make sure we can obtain the structure constants. 
  try 
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;

  basis := __A_Centroid(Eltseq(t), [Dimension(X) : X in Frame(t)], {a, b});

  // Get the correct representation.
  if 0 notin {a, b} then
    for i in [1..#basis] do
      basis[i][2] := Transpose(basis[i][2]);
    end for;
  end if;

  Nuke, basis := __MakeAlgebra(t, {a, b}, false, MatrixAlgebra, basis, "Nucleus");
  t`Nuclei[2][ind] := basis;

  // Sanity check
  if __SANITY_CHECK then
    // Preliminaries  
    printf "Running sanity check (Nucleus)\n";
    min := Min({a,b});
    max := Max({a,b});
    proj := [*Induce(Nuke, min), Induce(Nuke, max)*]; 
    dom_basis := CartesianProduct(<Basis(X) : X in Domain(t)>);

    // A function to only change one coordinate.
    MultByMat := function(x, B, a)
      y := x;
      y[Valence(t) - a] := y[Valence(t) - a]*B;
      return y;
    end function;

    // Checking satisfaction of (x_a - x_m), for all a in A - {m}.
    if min eq 0 then
      assert forall{nu : nu in Generators(Nuke) | forall{x : x in dom_basis | 
        MultByMat(x, nu @ proj[2], max) @ t eq (x @ t)*(nu @ proj[1]) \
        }};
    else
      assert forall{nu : nu in Generators(Nuke) | forall{x : x in dom_basis | 
        MultByMat(x, nu @ proj[2], max) @ t eq MultByMat(x, Transpose(nu @ proj[1]), min) @ t 
        }};
    end if;
  end if;

  return Nuke;
end intrinsic;

intrinsic SelfAdjointAlgebra( t::TenSpcElt, a::RngIntElt, b::RngIntElt ) 
  -> ModMatFld
{Returns the vector space of ab-self-adjoint operators for the tensor t.}
  // Make sure {a,b} make sense.
  require a ne b : "Integers must be distinct.";
  v := Valence(t);
  require {a,b} subset {0..v-1} : \
    "Integers must correspond to Cartesian factors.";
  if t`Cat`Contra then
    require 0 notin {a,b} : "Integers must be positive for cotensors.";
  end if;
  require Dimension(Frame(t)[v-a]) eq Dimension(Frame(t)[v-b]) : 
    "Given coordinates correspond to non-isomorphic spaces.";

  // Make sure we can obtain the structure constants. 
  try 
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;

  basis := __A_Centroid(Eltseq(t), [Dimension(X) : X in Frame(t)], {a, b} : 
    repeats := {{a, b}});

  // Quick fix.
  KSqMatSp := func< K, n | KMatrixSpace(K, n, n) >;
  return __MakeAlgebra(t, {a, b}, true, KSqMatSp, basis);
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
//                            Special names for bimaps
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
