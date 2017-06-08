K := Rationals();
L := LieAlgebra("A1", K);
T := AssociatorTensor(L);
T;

Eltseq(T);



AsMatrices(T, 3, 1)[1..4];

