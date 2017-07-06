A := MatrixAlgebra(Rationals(), 4);
t := AnticommutatorTensor(A);
t;
SystemOfForms(t)[1];
A.1*t*A.1;


s := (1/2)*t;
s;
A.1*s*A.1;


IsSymmetric(s);
JordanID := func< x, y | (x*s*y)*s*(x*s*x) - x*s*(y*s*(x*s*x)) >;
forall{ <x,y> : x in Basis(A), y in Basis(A) | \
    JordanIdentity(x, y) eq Codomain(s)!0 };

