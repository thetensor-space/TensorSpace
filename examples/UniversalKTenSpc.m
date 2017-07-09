K := Rationals();
S := [6, 5, 4, 3];
T := KTensorSpace(K, S);
T;


t := T![Random([-1, 0, 1]) : i in [1..Dimension(T)]];
t;
Parent(t);

