// Infix 
B := RandomTensor(GF(5),[4,3,5]);
B;
[3,2,0,1]*B*[1,1,2];
[1,0,0,0]*B;
B*[0,2,0];



// Product
G := SmallGroup(512,10^6);
B := pCentralTensor(G,2,1,1);
B;
U := LeftDomain(B);   //U2
V := RightDomain(B);  //U1
U![0,1,0,1,0] * V![1,0,0,0,0];
U!(G.2*G.4) * V!G.1;


H := sub< G | G.2,G.4 >;
U!H * V!G.1;
U!H * V!G;
