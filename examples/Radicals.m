K := Rationals();
A := MatrixAlgebra(K, 3);
T, phi := CommutatorTensor(A);
T;

R2 := Radical(T, 2);
R2.1 @@ phi;
Radical(T);


Image(T);
Coradical(T);
