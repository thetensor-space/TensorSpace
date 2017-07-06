K := GF(541);
V := VectorSpace(K, 10);
U := VectorSpace(K, 5);
mult := function(x)
  M := Matrix(3, 3, Eltseq(x[1])[2..10]);
  v := VectorSpace(K, 3)!(Eltseq(x[2])[[1,3,5]]);
  return Eltseq(v*M) cat [0,0];
end function;
t := Tensor([V, U, U], mult);
t;


IsFullyNondegenerate(t);
Image(t);


s, H := FullyNondegenerateTensor(s);
s;
H;

