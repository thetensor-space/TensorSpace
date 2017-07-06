K := GF(541);
U := KMatrixSpace(K,2,3);
my_prod := func< x | x[1]*Transpose(x[2])*x[3] >;
t := Tensor([U,U,U,U], my_prod );
t;


A := U![1,0,0,0,0,0];
A;

<A,A,A> @ t;  // A is a generalized idempotent


X := [Random(U) : i  in [1..5]];
X;

A := <X[1],X[2],X[3]> @ t;
B := <X[4],X[3],X[2]> @ t;
A, B;

<A, X[4], X[5]> @ t eq <X[1], B, X[5]> @ t;



l_asct := func< X | Eltseq(<<X[1], X[2], X[3]> @ t, X[4], X[5]> @ t \
    - <X[1], <X[4], X[3], X[2]> @ t, X[5]> @ t) >;
Lt := Tensor([* U : i in [0..5] *], l_asct);
Lt;

I := Image(Lt);
I;

Dimension(I);

