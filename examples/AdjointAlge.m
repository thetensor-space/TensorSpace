G := SmallGroup(3^7, 7000);
T := pCentralTensor(G);
T;


A := AdjointAlgebra(T);
A;
A.1;


RecognizeStarAlgebra(A);
SimpleParameters(A);
Star(A);

