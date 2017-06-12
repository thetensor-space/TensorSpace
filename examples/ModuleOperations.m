K := Rationals();
T := Tensor(K, [2, 2, 2], [1..8]);
S := Tensor(K, [2, 2, 2], &cat[[2, -1] : i in [1..4]]);
SystemOfForms(T);
SystemOfForms(S);


SystemOfForms(-T);
SystemOfForms((1/3)*S);
SystemOfForms(T+S);
SystemOfForms(T-2*S);

