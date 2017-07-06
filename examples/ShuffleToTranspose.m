t := Tensor(Rationals(), [2, 2, 1], [0, 1, -1, 0]);
t;
SystemOfForms(t);

s := Shuffle(t, [0,2,1]);
s;
SystemOfForms(s);

