J := Matrix(GF(9),[[0,1,-1],[1,-1,-1],[-1,-1,1]]);
M := DiagonalJoin(J,ZeroMatrix(GF(9),3,3));
M;

T := Tensor([M,-M],2,1);
T;

Image(T);

Radical(T);



ND := NondegenerateTensor(T);
ND;

FN := FullyNondegenerateTensor(T);
FN;

