O := OctonionAlgebra(GF(7), -1, -1, -1);
L := DerivationAlgebra(O); // Derivations as an algebra.
SemisimpleType(L);


T := Tensor(O);
T := ChangeTensorCategory(T, HomotopismCategory(3));
M := DerivationAlgebra(T); // Derivations as a tensor .
SemisimpleType(M/SolvableRadical(M));
