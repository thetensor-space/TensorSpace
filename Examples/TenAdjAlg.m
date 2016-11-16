V := VectorSpace(GF(5),10);
E := ExteriorCotensorSpace(V,2);
E;

T := Random(E);
S := Random(E);
CT := SubtensorSpace(E,[T,S]);
T2 := AsTensor(CT);
T2;

A := AdjointAlgebra(T2);
RecognizeStarAlgebra(A);
Star(A);

