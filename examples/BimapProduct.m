G := SmallGroup(512, 10^6);
T := pCentralTensor(G);
T;
U := LeftDomain(T);
V := RightDomain(T);
U;
V;


x := U!(G.1*G.2*G.4);
y := V![1,0,0,0,0];
x;
y;
x*y;


H := sub< G | G.2,G.4 >;
U!H * V!G.1;
U!H * V;

