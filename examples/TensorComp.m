A := MatrixAlgebra(GF(3), 3);
JacobiID := func< x | x[1]*x[2]*x[3]+x[2]*x[3]*x[1]+x[3]*x[1]*x[2] >;
Cat := TensorCategory([1 : i in [0..3]], {{0..3}});
T, Maps := Tensor([A : i in [0..3]], JacobiID, Cat);
T;
TensorCategory(T);


phi := Maps[1];
T * (phi^-1);
T * (phi^-1) eq T;


E := [A.1, A.2^-1*A.1*A.2, A.2^-2*A.1*A.2^2];
E;
f := map< A -> A | x :-> &+[ E[i]*x*E[i] : i in [1..3] ] >;
f;
S := T*(phi^-1*f);
S;
S eq T;


F := Tensor([A, A], func< x | x[1]@f >);
F;
T * F eq S;

