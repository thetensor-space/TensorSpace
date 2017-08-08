Q := QuaternionAlgebra(Rationals(), 1,1);
Trace(Q!1);        
GenericTrace(Q!1);
Q := QuaternionAlgebra(GF(2), 1,1);  
Trace(Q!1);
GenericTrace(Q!1);



J := ExceptionalJordanCSA(GF(5));
p := GenericMinimumPolynomial(J.3+J.12);
Rx := AsMatrices(Tensor(J), 2,0);	// yR_x = y*x.
q := MinimalPolynomial(Rx[3]+Rx[12]); 
Degree(p);
Degree(q);
q mod p;

