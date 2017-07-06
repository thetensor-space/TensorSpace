K := Rationals();
A := MatrixAlgebra(K, 3);
t, phi := CommutatorTensor(A);
t;

R2 := Radical(t, 2);
R2.1 @@ phi;
Radical(t);


Image(t);
Coradical(t);
