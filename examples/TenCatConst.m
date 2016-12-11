Cat := TensorCategory([1,-1,0],{{0},{1},{2}});
Cat;

TS := KTensorSpace(GF(5),[5,3,4],Cat);
TS;
TensorCategory(TS);

IsContravariant(TS);



Cat := HomotopismCategory(2 : Contravariant := true);
Cat;
T := Tensor(GF(5),[2,2],[1..4],Cat);
T;

