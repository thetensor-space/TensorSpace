U := VectorSpace(Rationals(),4);
V := VectorSpace(Rationals(),3);
W := VectorSpace(Rationals(),2);
T := TensorSpace([U, V, W]);
t := T![1..24];
t;
Slice(t, [{1..4},{1..3},{1..2}]) eq Eltseq(t);



[ U.i*t*V.2 : i in [1..4]];
Slice(t, [{1..4},{2},{1}]); 


Slice(t, [{1..4},{2},{-1}]);


Slice(t, [{1..4},{2},{-1,2}]);


s := InducedTensor(t, [{1..4}, {2}, {1,2}]);
s;
s2 := Tensor([4, 1, 2], Slice(t, [{1..4}, {2}, {1,2}]));
s2;

s eq s2;
Eltseq(s);

