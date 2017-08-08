K := Rationals();
T := KTensorSpace(K, [2,2,1]);
T;
S := sub< T | T.1, T.2+T.3, T.4 >;
S;
IsSymmetric(S);


A := sub< T | T.2-T.3 >;
A;
IsAlternating(A);


IsSubtensorSpace(S, A);

