t := Tensor(Rationals(), [4,3,2], [1..24]);
t;
AsMatrices(t, 1, 0);


SliceAsMatrices(t, [{1,-1}, {1,-1}, {1,2}], 1, 0);

