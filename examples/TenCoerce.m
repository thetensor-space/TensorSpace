TS := KTensorSpace( GF(2), [2,3,2] );
TS;

S := [ Random(GF(2)) : i in [1..12] ];
T := TS!S;
T;

T eq Tensor(GF(2),[2,3,2],S);



V := VectorSpace(Rationals(),10);
SS := SymmetricCotensorSpace(V,3);
SS;

CT := SubtensorSpace(SS,SS![1..1000]);
CT;

CT subset SS;
CT.1 in SS;
SS.2 in CT;

