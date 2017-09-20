C := TensorCategory([1, 1, 0], {{0}, {1,2}});
C;

T := KTensorSpace(GF(2), [10, 10, 2], C);
T;

t := T![1..200];
t;


Sprint(C);

Sprint(T);

Sprint(t);

