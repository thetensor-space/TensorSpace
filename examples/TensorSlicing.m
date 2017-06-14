U := VectorSpace(Rationals(),4);
V := VectorSpace(Rationals(),3);
W := VectorSpace(Rationals(),2);
TS := TensorSpace([U, V, W]);
T := TS![1..24];
T;
Slice(T, [{1..4},{1..3},{1..2}]) eq Eltseq(T);



[ U.i*T*V.2 : i in [1..4]];
Slice(T, [{1..4},{2},{1}]); 


Slice(T, [{1..4},{2},{-1}]);


Slice(T, [{1..4},{2},{-1,2}]);


S := InducedTensor(T, [{1..4}, {2}, {1,2}]);
S;
S2 := Tensor([4, 1, 2], Slice(T, [{1..4}, {2}, {1,2}]));
S2;

S eq S2;
Eltseq(S);

