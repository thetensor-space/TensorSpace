A := MatrixAlgebra(Rationals(), 4);
J := AnticommutatorTensor(A);
J;
SystemOfForms(J)[1];
A.1*J*A.1;


T := (1/2)*J;
T;
A.1*T*A.1;


IsSymmetric(T);
JordanID := func< x, y | (x*T*y)*T*(x*T*x) - x*T*(y*T*(x*T*x)) >;
forall{ <x,y> : x in Basis(A), y in Basis(A) | \
    JordanIdentity(x, y) eq Codomain(T)!0 };

