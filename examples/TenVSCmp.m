L := LieAlgebra("D4",GF(5));
T := Tensor(L); 
T;
<L.2,L.11> @ T;

S := TensorOnVectorSpaces(T);
S;
V := Domain(S)[1];
<L.2,L.11> @ S eq <V.2,V.11> @ S;



AF := AssociatedForm(S);
AF;
Eltseq(AF) eq Eltseq(S);

<L.2,L.11,L.1> @ AF;
<L.2,L.11,L.2 > @ AF;

U := Shuffle(AF,[3,1,2,0]);
U;

Cmp := Compress(U);
Shf := Shuffle(S,[2,0,1]);
Cmp eq Shf;

