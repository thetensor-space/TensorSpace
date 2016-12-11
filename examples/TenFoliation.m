T := RandomTensor( GF(7), [2,3,4] );
Foliation(T,0);

Slice(T,[{1,2},{1..3},{3}]); // row 3

Slice(T,[{2},{1},{1..4}]); // col 4




CT := AsCotensorSpace(T);
CT;

S := Random(CT);
MS := KMatrixSpace(GF(7),2,3);
SystemOfForms(S) subset sub<MS|SystemOfForms(T)>;


TS := AsTensorSpace(T,1);
TS;

S := Random(TS);
MS := KMatrixSpace(GF(7),2,4);
AsMatrices(S,1,0) subset sub<MS|AsMatrices(T,2,0)>;

