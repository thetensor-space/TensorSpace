L := LieAlgebra("A3", GF(3));
t := Tensor(L);
t;
AlternatingTensor(t) eq t;
