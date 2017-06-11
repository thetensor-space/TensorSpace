A := MatrixAlgebra(Rationals(), 4);
C := CommutatorTensor(A);
C;
IsAlternating(C); // [X, X] = 0?


M := A![1,0,0,0,0,1,0,0,0,0,-1,0,0,0,0,-1];
M;
Dimension(A) - Dimension(<M, A> @ C);
