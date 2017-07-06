t := KTensorSpace(GF(5), [5, 5, 4])!0;
for i in [1..4] do
  Assign(~t, [i, i+1, i], 1);   // 1s above diag
  Assign(~t, [i+1, i, i], -1);  // 4s below diag
end for;
t;
IsAlternating(t);


SystemOfForms(t);
IsFullyNondegenerate(t);


H := HeisenbergGroup(t);
LMGOrder(LMGCenter(H)) eq 5^4;
s := pCentralTensor(H, 5, 1, 1);
s;


PgrpCat := TensorCategory([1, 1, 1], {{2,1},{0}});
PgrpCat;
ChangeTensorCategory(~t, PgrpCat);
H := HeisenbergGroup(t);
LMGOrder(LMGCenter(H)) eq 5^4;
s := pCentralTensor(H, 5, 1, 1);
s;


SystemOfForms(s);

