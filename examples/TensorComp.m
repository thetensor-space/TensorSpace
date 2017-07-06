A := MatrixAlgebra(GF(3), 3);
JacobiID := func< x | x[1]*x[2]*x[3]+x[2]*x[3]*x[1]+x[3]*x[1]*x[2] >;
Cat := TensorCategory([1 : i in [0..3]], {{0..3}});
t, Maps := Tensor([A : i in [0..3]], JacobiID, Cat);
t;
TensorCategory(t);


phi := Maps[1];
t * (phi^-1);
t * (phi^-1) eq t;


E := [A.1, A.2^-1*A.1*A.2, A.2^-2*A.1*A.2^2];
E;
f := map< A -> A | x :-> &+[ E[i]*x*E[i] : i in [1..3] ] >;
f;
s := t*(phi^-1*f);
s;
s eq t;


g := Tensor([A, A], func< x | x[1]@f >);
g;
t * g eq s;

