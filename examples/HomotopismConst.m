T := KTensorSpace(GF(3), [3,3,3]);
t := T.1+T.14+T.27;
SystemOfForms(t);
s := (T.4+T.10)+(T.8+T.20)+(T.18+T.24);
SystemOfForms(s);


P := PermutationMatrix(GF(3), [2,1,3]);
H := Homotopism(t, t, [*P, P, P*]);
H;


IsHomotopism(s, s, [*P, P, P*]);
