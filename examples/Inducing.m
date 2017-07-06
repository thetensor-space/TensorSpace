t := Tensor(GF(3), [2, 2, 1], [0, 1, 2, 0]);
t;
IsAlternating(t);


D := DerivationAlgebra(t);
D.1;
D.2;
D1, pi := Induce(D, 1);
D1;
pi;


D1.1;
D1.2;

