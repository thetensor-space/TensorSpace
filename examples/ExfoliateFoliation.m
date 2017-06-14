K := Rationals();
Forms := [Matrix(K, 3, 2, [6*i+1..6*(i+1)]) : i in [0..3]];
T := Tensor(Forms, 1, 0);
T;


F2 := Foliation(T, 2);
F2;
R := Nullspace(F2);
R;


R*T;
Dimension(R*T);

