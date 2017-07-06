A := MatrixAlgebra(Rationals(), 4);
t := CommutatorTensor(A);
t;
IsAlternating(t); // [X, X] = 0?


M := A![1,0,0,0,0,1,0,0,0,0,-1,0,0,0,0,-1];
M;
Dimension(A) - Dimension(<M, A> @ t);
