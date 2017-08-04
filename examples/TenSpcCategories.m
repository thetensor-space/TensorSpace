T := KTensorSpace(Rationals(), [4,4,4]);
T;

TensorCategory(T);
C := TensorCategory([1,1,-1], {{0},{1,2}});
C;

ChangeTensorCategory(~T, C);
T;
TensorCategory(T);

