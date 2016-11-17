TS := KTensorSpace( GF(23), [3,4,5,6] );
TS;

Valence(TS);
Frame(TS);
TensorCategory(TS);

Cat := TensorCategory([1,1,-1,-1],{{0},{1},{2},{3}});
ChangeTensorCategory(~TS,Cat);
TensorCategory(TS);


V := VectorSpace( GF(3), 5 );
S := SymmetricCotensorSpace(V,3);
S;
UniversalCotensorSpace(S);

IsSymmetric(S);

