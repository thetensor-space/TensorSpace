T := KTensorSpace( GF(2), [2,3,2] );
T;

S := [ 1 : i in [1..12] ];
t := T!S;
t;

t eq Tensor(GF(2), [2,3,2], S);

T!0 in T;
SystemOfForms(T!0);

