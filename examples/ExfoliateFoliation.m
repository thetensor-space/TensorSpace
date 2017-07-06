K := Rationals();
Forms := [Matrix(K, 3, 2, [6*i+1..6*(i+1)]) : i in [0..3]];
t := Tensor(Forms, 1, 0);
t;


F2 := Foliation(t, 2);
F2;
R := Nullspace(F2);
R;


R*t;
Dimension(R*t);

