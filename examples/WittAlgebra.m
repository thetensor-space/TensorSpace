p := 5;
R<x> := PolynomialRing(GF(p));
I := ideal< R | x^p >;
Q := quo< R | I >;
Q;
T := Tensor(Q);
T;
TensorCategory(T);


D := DerivationAlgebra(T);
IsSimple(D);
Dimension(D);
KillingForm(D);

