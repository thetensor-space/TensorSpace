TS := KTensorSpace(Rationals(),[ i : i in [3..7] ]);
TS;

TS.1;


R := pAdicRing(3,6);
Fr := [RSpace(R,5), sub<RSpace(R,3)|[0,1,0],[0,0,1]>,\
  RSpace(R,2)];
TS2 := TensorSpace(Fr);
TS2;

TS2.10;


TS3 := TensorSpace( VectorSpace(GF(3),3), 2, 4 );
TS3;

TensorCategory(TS3);
