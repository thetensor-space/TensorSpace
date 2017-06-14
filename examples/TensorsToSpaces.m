T := Tensor(Rationals(), [5,4,3,2], [1..120]);
T;
TS := AsTensorSpace(T, 3);
TS;


F := [SliceAsMatrices(T, [{k},{1..4},{1..3},{1,2}], 2, 1) : \
    k in [1..5]];


F[1];
F[2];


F[3];
Tensor(F[3], 2, 1) eq 2*Tensor(F[2], 2, 1) - Tensor(F[1], 2, 1);
Tensor(F[4], 2, 1) eq 3*Tensor(F[2], 2, 1) - 2*Tensor(F[1], 2, 1);
Tensor(F[5], 2, 1) eq 4*Tensor(F[2], 2, 1) - 3*Tensor(F[1], 2, 1);


SystemOfForms(TS.1) eq F[1];
SystemOfForms(TS.2) eq F[2];
Radical(T, 3);

