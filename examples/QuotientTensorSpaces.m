K := Rationals();
T := KTensorSpace(K, [2,2,1]);
T;
S := sub< T | T.1, T.2+T.3, T.4 >;
A := sub< T | T.2-T.3 >;


Q := T/A;
Q;
SystemOfForms(Q.1);
SystemOfForms(Q.2);
SystemOfForms(Q.3);

