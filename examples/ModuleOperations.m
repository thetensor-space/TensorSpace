K := Rationals();
t := Tensor(K, [2, 2, 2], [1..8]);
s := Tensor(K, [2, 2, 2], &cat[[2, -1] : i in [1..4]]);
SystemOfForms(t);
SystemOfForms(s);


SystemOfForms(-t);
SystemOfForms((1/3)*s);
SystemOfForms(t+s);
SystemOfForms(t-2*s);

