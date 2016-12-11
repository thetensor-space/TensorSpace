TS := KTensorSpace( GF(9), [2,2,2,2] );
TS;

Ngens(TS);
#TS eq 9^Ngens(TS);

Eltseq(TS.2);



T := RandomTensor(GF(3),[2,2,2]);
T;

Cat := CotensorCategory([1,1,1],{{1,2,3}});
T := RandomTensor(GF(3),[2,2,2],Cat);
T;

