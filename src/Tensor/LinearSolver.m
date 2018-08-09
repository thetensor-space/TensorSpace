/* 
    Copyright 2018 Joshua Maglione, James B. Wilson.
    Distributed under GNU GPLv3.
*/


import "TensorData.m" : __GetForms;



/* 
  Test file to see how well this works. 
  This is just data manipulation and very basic linear algebra. Ideally, this is
  programmed at a low level.
*/


/*
  Input are three matrices where the input denotes 
    [ A  B ]
    [ I  C ].
  We will add the rows of C to B via the rows of A. The output is a matrix D
    [ 0  D ]
    [ I  C ].
  We assume the dimensions are correct. 
*/
__BackSolverOLD := function(A, B, C)
  A_rows := [A[i] : i in [1..Nrows(A)]];
  B_rows := [B[i] : i in [1..Nrows(B)]];
  C_rows := [C[i] : i in [1..Nrows(C)]];
  for i in [1..Nrows(A)] do
    r := A_rows[i]; 
    B_rows[i] +:= &+[r[j]*C_rows[j] : j in [1..Degree(r)]];
  end for;
  return Matrix(B_rows);
end function;


/*
  Input are two matrices where the input denotes 
    [ A ]
    [ B ],
  where B is in RREF.  Return the matrix C such that 
    [ C ] 
    [ B ]
  is in RREF modulo row permutations.
*/
__BackSolver := function(A, B)
  A_rows := [A[i] : i in [1..Nrows(A)]];
  B_rows := [B[i] : i in [1..Nrows(B)]];
  for r in B_rows do
    if exists(j){j : j in [1..Degree(r)] | r[j] ne 0} then
      for i in [1..#A_rows] do
        A_rows[i] +:= -(A_rows[i][j]) * r;
      end for;
    end if;
  end for;
  return A;
end function;


// Solve XA - AY^t = 0.
AdjointSolver := function(t)
  s := Eltseq(t);
  spaces := Frame(t);
  dims := [Dimension(X) : X in spaces];
  rightBlocks := __GetForms(s, dims, 1, 0 : op := true);
  assert #rightBlocks eq dims[1];
  leftBlocks := __GetForms(s, dims, 2, 0 : op := true);
  assert #leftBlocks eq dims[2];

  /*
    Outline of the algorithm:
      Step 1. Get the right blocks into RREF
      Step 2. Propagate the transformations to the left blocks. 
      Step 3. Get the bottom blocks in the left blocks into RREF.
      Step 4. Back solve.
      Step 5. Extract data.
  */

  // Step 1.
  rrefRight := [];
  transforms := [];
  for i in [1..dims[1]] do
    E, T := EchelonForm(rightBlocks[i]);
    Append(~rrefRight, E);
    Append(~transforms, -T);
  end for;

  // Step 2.
  transformBlocks := [[transforms[i] * leftBlocks[j] : j in [1..dims[2]]] : 
    i in [1..dims[1]]];

  // Step 3.
  ranksRight := [Rank(E) : E in rrefRight];
  bottomLeft := [*[*ExtractBlock(X, ranksRight[i]+1, 1, dims[3]-ranksRight[i], 
    dims[1]) : X in transformBlocks[i]*] : i in [1..dims[1]]*];
  topLeft := [*[*ExtractBlock(X, 1, 1, ranksRight[i], dims[1]) : 
    X in transformBlocks[i]*] : i in [1..dims[1]]*];
  rrefBottomLeft := [*[*EchelonForm(bottomLeft[i][j]) : j in [1..dims[2]]*] : 
    i in [1..dims[1]]*];

  // Step 4. 
  rrefTopLeft := [*[*__BackSolver(topLeft[i][j], rrefBottomLeft[i][j]) : 
    j in [1..dims[2]]*] : i in [1..dims[1]]*];

  // Step 5. 

  return 0;
end function;
