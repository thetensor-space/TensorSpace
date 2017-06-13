G := SmallGroup(512, 10^6);
T := pCentralTensor(G);
T;
U := LeftDomain(T);
V := RightDomain(T);
U;
V;


V!G.1 eq V![1,0,0,0,0];
Parent(U);
Parent(U) eq T;

