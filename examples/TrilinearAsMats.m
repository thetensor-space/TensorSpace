K := Rationals();
L := LieAlgebra("A1", K);
t := AssociatorTensor(L);
t;

Eltseq(t);



AsMatrices(t, 3, 1)[1..4];

