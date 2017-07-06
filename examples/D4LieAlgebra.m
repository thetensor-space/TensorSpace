L := LieAlgebra("D4", GF(11));
t := Tensor(L);
t;
IsAlternating(t);
TensorCategory(t);


D := DerivationAlgebra(t);
Dimension(D);
SemisimpleType(D);


ChangeTensorCategory(~t, HomotopismCategory(3));
t;
TensorCategory(t);


D := DerivationAlgebra(t);
Dimension(D);
R := SolvableRadical(D);
SemisimpleType(D/R);

