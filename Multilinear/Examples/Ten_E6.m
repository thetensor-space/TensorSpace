K := GF(7);  	// Use a field of char not 2 or 3
J := ExceptionalJordanCSA(K);
T := Tensor(J);
L := sub<MatrixLieAlgebra(K,27) | AsMatrices(T,2,0)>;
E6 := L*L; 
SemisimpleType(E6);
M := RModule(E6);
IsIrreducible(M);
