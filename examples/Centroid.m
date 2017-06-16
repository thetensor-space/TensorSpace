A := MatrixAlgebra(Rationals(), 4);
R<x> := PolynomialRing(Rationals());
F := sub< A | A!1, CompanionMatrix(x^4-x^2-2) >;
F;
T := Tensor(F);
T;


C := Centroid(T);
C;
sub< C | C.1 > eq C;
forall{ c : c in Generators(C) | IsInvertible(c) };
IsCommutative(C);
MinimalPolynomial(C.1);
Factorization(MinimalPolynomial(C.1));

