K := GF(541);
U := KMatrixSpace(K,2,3);
my_prod := func< x | x[1]*Transpose(x[2])*x[3] >;
T := Tensor([U,U,U,U], my_prod );
T;
A := U![1,0,0,0,0,0];
<A,A,A>@T;  // A is a generalized idempotent

X := [Random(U) : i  in [1..5]];
<<X[1],X[2],X[3]>@T,X[4],X[5]>@T eq \
    <X[1],<X[4],X[3],X[2]>@T,X[5]>@T;

my_left_asct := func<X|<<X[1],X[2],X[3]>@T,X[4],X[5]>@T\
    - <X[1],<X[4],X[3],X[2]>@T,X[5]>@T >;
LT := Tensor([U: i in [0..5]], my_left_asct);
I := Image(LT);
Dimension(I);

