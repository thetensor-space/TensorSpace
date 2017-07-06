G := SmallGroup(3^7, 7000);
t := pCentralTensor(G);
t;


A := AdjointAlgebra(t);
A;
A.1;


RecognizeStarAlgebra(A);
SimpleParameters(A);
Star(A);

