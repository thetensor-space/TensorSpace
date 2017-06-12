L := LieAlgebra("B3", GF(5));
T := Tensor(L); 
T;
AF := AssociatedForm(T);
AF;
<L.2, L.11> @ T;
<L.2, L.11, L.2> @ AF;
<L.2, L.11, L> @ AF;


S := Shuffle(AF, [3,1,2,0]);
S;
C := Compress(S);
C;
C eq Shuffle(T, [2, 0, 1]);

