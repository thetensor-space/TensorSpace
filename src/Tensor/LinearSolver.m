/* 
    Copyright 2018 Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


import "TensorData.m" : __GetForms;



/* 
  Test file to see how well this works. 
  This is just data manipulation and very basic linear algebra. Ideally, this is
  programmed at a low level.
*/

/*
  Given: seq - the structure constants of a tensor. Type: [FldElt]
         dims - the dimensions of the frame, starting at U_vav and ending at 
            U_0. Type: [RngIntElt]

  Return: basis - a basis for the {1, 0}-nucleus of a tensor. Type: [Tup];
            here Tup is a pair of matrices in End(U_1) x End(U_0).

  Complexity: O(PI^2 * d0^2 / d1), where di = dim(U_i) and 
      PI = d0 * d1 * ... * dvav.
*/
Nuc10 := function(seq, dims) 
  // Initial setup.
  d := &*(dims);
  d1 := dims[#dims-1];
  d0 := dims[#dims];
  c := d div (d1 * d0);
  K := Parent(seq[1]);
  Id0 := IdentityMatrix(K, d0);
  ZC := ZeroMatrix(K, c * d0, 1);

  // Constructing the matrices M^(I).
  Mats := __GetForms(seq, dims, 1, 0);
  // The matrix in the first pillar in each stripe, before a Kronecker product.
  FPillars_part := [Matrix(K, [Eltseq(Mats[k][i]) : 
    k in [1..c]]) : i in [1..d1]];
  // Second pillar
  Mats := [Transpose(X) : X in Mats];
  SPillar := -Matrix(K, &cat[[Eltseq(Mats[k][i]) : 
    k in [1..c]] : i in [1..d0]]);
  delete Mats;

  // Step 1: Get second pillar in RREF.
  E_SPillar, T_SPillar := EchelonForm(SPillar);
  r := Rank(E_SPillar);
  z := Nrows(E_SPillar) - r;
  delete SPillar;

  // Columns in the first pillar containing pivots.
  pivots := [];
  // First pillar
  FPillars := [];
  // Now we run through each of the stripes of the first pillar.
  for i in [1..d1] do
    // Step 2a: Propagate T_SPillar to each stripe.
    FPillar_i := KroneckerProduct(Id0, FPillars_part[1]);
    FPillar_i := T_SPillar*FPillar_i;
    FPillars_part := FPillars_part[2..#FPillars_part];

    // Step 2b: Forward solve.
    for j in pivots do
      // Replace the columns below a pivot with the 0 column.
      InsertBlock(~FPillar_i, ZC, 1, j);
    end for;

    // Step 3: Get the lower part of the ith first pillar in RREF.
    FPillar_i_lower := ExtractBlock(FPillar_i, r+1, 1, z, Ncols(FPillar_i));
    E_FP_i_l := EchelonForm(FPillar_i_lower); // Main bottleneck
    // Store the first pillar for the ith stripe after RREF.
    Append(~FPillars, InsertBlock(FPillar_i, E_FP_i_l, r+1, 1));

    // Step 4a: Find the columns in the first pillar containing pivots. 
    new := []; // New pivots found for this i.
    r_i := Rank(E_FP_i_l);
    j := 1;
    // Search for pivots 
    while #new lt r_i do
      if E_FP_i_l[#new + 1][j] ne 0 then
        Append(~new, j);
      end if;
      pivots cat:= new;
      j +:= 1;
    end while;

    // Step 4b: Back solve.
    for j in [1..i-1] do
      M := FPillars[j];
      for k in new do 
        // Replace the columns above a pivot with the 0 column.
        InsertBlock(~M, ZC, 1, k);
      end for;
      FPillars[j] := M;
    end for;
  end for;

  // Step 5: Construct a basis.
  return 0;
end function;













intrinsic NEWNUKE( t::TenSpcElt ) -> RngIntElt
{A better solver?}
  seq := Eltseq(t);
  dims := [Dimension(X) : X in Frame(t)];
  return Nuc10(seq, dims);
end intrinsic;
