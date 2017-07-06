K := RealField(5);
V := VectorSpace(K, 3);
CP := function(x)
  return V![x[1][2]*x[2][3] - x[1][3]*x[2][2], \
    x[1][3]*x[2][1] - x[1][1]*x[2][3], \
    x[1][1]*x[2][2] - x[1][2]*x[2][1] ];
end function;
t := Tensor([V, V, V], CP);
t;

// test that i x j = k
<[1,0,0], [0,1,0]> @ t eq V.3;

