F := IdentityMatrix(Rationals(),2);
J := JordanSpinAlgebra(F);
T := Tensor(J); 
R := AsMatrices( T, 2,0); 
R[1];   // Is J.1 the identity?
J.2*J.2 eq J.1;  // J.2^2=1?
J.2*J.3 eq 0;	 // Yet J.2 is a zero-divisor.
e := (1/2)*(J.1+J.2);             
e^2 eq e;  // An idempotent of J?


Re := (1/2)*(R[1]+R[2]);
Eigenvalues(Re);  //Pierce decomposition has 0,1, & 1/2 eigenspaces.                                                                                                                

