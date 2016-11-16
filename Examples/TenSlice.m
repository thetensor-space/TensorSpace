U := VectorSpace(Rationals(),4);
V := VectorSpace(Rationals(),3);
W := VectorSpace(Rationals(),2);
TS := TensorSpace([U,V,W]);
T := TS![ i : i in [1..24] ];
Slice(T,[{1..4},{1..3},{1..2}]);  // structure constants



Slice(T,[{1..4},{2},{1}]); 

W1 := VectorSpace(Rationals(),1);
pi := hom< W -> W1 | <W.1,W1.1>, <W.2,W1!0> >; // project onto 1st coord
Eltseq((T*V.2)*pi);



T_ind := InducedTensor(T,[{1..4},{2},{1}]);
T_ind;
S := (T*V.2)*pi;
S;

Compress(T_ind) eq S;

