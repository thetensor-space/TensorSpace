K := RealField(5);
V := VectorSpace(K, 3);
CP := function(x)
  return V![x[1][2]*x[2][3] - x[1][3]*x[2][2], \
    x[1][3]*x[2][1] - x[1][1]*x[2][3], \
    x[1][1]*x[2][2] - x[1][2]*x[2][1] ];
end function;
T := Tensor([V, V, V], CP);
T;

// test that i x j = k
<[1,0,0], [0,1,0]> @ T eq V.3;

