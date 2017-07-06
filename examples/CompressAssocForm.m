L := LieAlgebra("B3", GF(5));
t := Tensor(L); 
t;
s := AssociatedForm(t);
s;
<L.2, L.11> @ t;
<L.2, L.11, L.2> @ s;
<L.2, L.11, L> @ s;


shf := Shuffle(s, [3,1,2,0]);
shf;
cmp := Compress(shf);
cmp;
cmp eq Shuffle(t, [2, 0, 1]);

