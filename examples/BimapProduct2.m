G := SmallGroup(512, 10^6);
t := pCentralTensor(G);
t;
U := LeftDomain(t);
V := RightDomain(t);
U;
V;


V!G.1 eq V![1,0,0,0,0];
Parent(U);
Parent(U) eq t;

