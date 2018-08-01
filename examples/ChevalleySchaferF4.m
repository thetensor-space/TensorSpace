J := ExceptionalJordanCSA(Rationals());
T := Tensor(J);                                     
T := ChangeTensorCategory(T, HomotopismCategory(3));
D := DerivationAlgebra(T);
D2 := Codomain(Induce(D, 2));		// Represent D on U2.
F4 := D2*D2;			              // Commutator.
SemisimpleType(F4);
F4;                             // F4 represented on a 27-dim module.


