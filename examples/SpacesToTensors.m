t := Tensor(Rationals(), [5,4,3,2], [1..120]);
t;
T := AsTensorSpace(t, 3);
T;


s := AsTensor(T);
s;
Radical(s, 3);


AsMatrices(s, 2, 1);

