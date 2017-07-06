p := 5;
R<x> := PolynomialRing(GF(p));
I := ideal< R | x^p >;
Q := quo< R | I >;
Q;
t := Tensor(Q);
t;
TensorCategory(t);


D := DerivationAlgebra(t);
IsSimple(D);
Dimension(D);
KillingForm(D);

