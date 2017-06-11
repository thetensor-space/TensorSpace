L := LieAlgebra("D4", GF(11));
T := Tensor(L);
T;
IsAlternating(T);
TensorCategory(T);


D := DerivationAlgebra(T);
Dimension(D);
SemisimpleType(D);


ChangeTensorCategory(~T, HomotopismCategory(3));
T;
TensorCategory(T);


D := DerivationAlgebra(T);
Dimension(D);
R := SolvableRadical(D);
SemisimpleType(D/R);

