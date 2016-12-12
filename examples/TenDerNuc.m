H := QuaternionAlgebra(Rationals(),-1,-1);
T := Tensor(H);                           
T;
D := DerivationAlgebra(T);
SemisimpleType(D);


ChangeTensorCategory(~T,HomotopismCategory(3));
N := Nucleus(T,2,1);
Dimension(N);
N.1^2 eq N!-1;
N.2^2 eq N!-1;
N.1*N.2 eq -N.2*N.1;

