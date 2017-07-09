R := Integers();
S := [* RMatrixSpace(R, 2, 3), RSpace(R, 5), RMatrixSpace(R, 2, 2), \
    RSpace(R, 3) *];
T := TensorSpace(S);
T;


x := < X!0 : X in S[1..3] >;
x;
x @ T;

