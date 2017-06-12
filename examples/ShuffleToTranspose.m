T := Tensor(Rationals(), [2, 2, 1], [0, 1, -1, 0]);
T;
SystemOfForms(T);

S := Shuffle(T, [0,2,1]);
S;
SystemOfForms(S);

