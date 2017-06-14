T := Tensor(Rationals(), [4,3,2], [1..24]);
T;
AsMatrices(T, 1, 0);


SliceAsMatrices(T, [{1,-1}, {1,-1}, {1,2}], 1, 0);

