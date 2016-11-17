A := MatrixAlgebra(Rationals(),5);
AC := CommutatorTensor(A);
IsAlternating(AC); // [X, X] = 0?


O := OctonionAlgebra(GF(541),-1,-1,-1);
T := AssociatorTensor(O);
<Random(O),Random(O),Random(O)> @ T eq 0;


a := Random(O); 
b := Random(O); 
<a,a,b> @ T eq 0;
IsAlternating(T);

