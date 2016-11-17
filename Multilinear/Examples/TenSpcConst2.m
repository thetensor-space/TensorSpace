TS := KTensorSpace(GF(3), [3,3,3,2]);
TS;

SS := SymmetricSpace(TS);
AsMatrices(Random(SS),3,2);


V := VectorSpace(GF(25),6);
E := ExteriorCotensorSpace(V,4);
E;

T := Random(E);
IsAlternating(T);

