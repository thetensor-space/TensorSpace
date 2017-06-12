L := LieAlgebra("A3", GF(3));
T := Tensor(L);
T;
AlternatingTensor(T) eq T;
