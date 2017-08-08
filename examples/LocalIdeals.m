A := OctonionAlgebra(Rationals(), -1, -1, -1);
t := Tensor(A);
t;
H_gens := [A.i : i in [1..4]];
t2 := Subtensor(t, [*H_gens, H_gens, H_gens*]);
s := Subtensor(t, [* A.2, [A.1, A.4], A!0 *]);
s;


s1 := LocalIdeal(t, s, {2});
Codomain(s1);
s2 := LocalIdeal(t2, s, {2});
Codomain(s2);

