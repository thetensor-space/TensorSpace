Fr := [ KMatrixSpace(GF(3),2,3),
  KMatrixSpace(GF(3),3,2),KMatrixSpace(GF(3),2,2) ];
F := func< x | x[1]*x[2] >;
T := Tensor(Fr,F);
T;

TS := Parent(T);
TS;

D := DerivationClosure(TS,T);
D;

