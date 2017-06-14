T := Tensor(Rationals(), [5,4,3,2], [1..120]);
T;
TS := AsTensorSpace(T, 3);
TS;


S := AsTensor(TS);
S;
Radical(S, 3);


AsMatrices(S, 2, 1);

