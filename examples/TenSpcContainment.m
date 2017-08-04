T := KTensorSpace(GF(2), [4,4,4]);
T;

T2 := KTensorSpace(GF(2), [4,1,4,1,4]);
T2;

S := sub< T | T.2, T.4, T.8 >;
S;


S subset T2;
S2 := T2!S;
S2 subset T2;
S2 subset T;

