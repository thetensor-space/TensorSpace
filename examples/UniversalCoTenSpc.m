K := Rationals();
S := [* KSpace(K, 3), MatrixAlgebra(K, 3), KMatrixSpace(K, 2, 3) *];
S;
T := CotensorSpace(S);
T;


t := T.3;
t;
Eltseq(t);

