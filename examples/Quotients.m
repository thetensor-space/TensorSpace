K := Rationals();
F := [*KMatrixSpace(K, 3, 2), VectorSpace(K, 3), VectorSpace(K, 3)*];
mult := function(x)
  return Transpose(x[1]*Matrix(2, 1, Eltseq(x[2])[2..3]));
end function;
t := Tensor(F, mult);
t;
s := Subtensor(t, [*[F[1].1, F[1].4], F[2], F[3]*]);
s;
IsFullyNondegenerate(s);


r := Ideal(t, [*F[1]!0, F[2].1, F[3].3*]);
r;
IsIdeal(t, r);


q := s/r;
q;
IsFullyNondegenerate(q);

