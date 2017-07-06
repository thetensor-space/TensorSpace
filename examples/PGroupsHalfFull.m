t := Tensor(GF(3), [4, 4, 3], &cat[[1,0,0,1] : i in [1..12]]);
t := AlternatingTensor(t);
t;
Radical(t);
Image(t);
SystemOfForms(t);


G := HeisenbergGroup(t);
LMGOrder(G) eq 3^11;
s := pCentralTensor(G);
s;
SystemOfForms(s);

