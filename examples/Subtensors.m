A := OctonionAlgebra(Rationals(), -1, -1, -1);
t := Tensor(A);
t;
H := sub< A | A.1, A.2, A.3, A.4 >;
H;



H_gens := [A.i : i in [1..4]];
s := Subtensor(t, [*H_gens, H_gens, A!0*]);
s;


s2 := Tensor(H);
s2;
s eq s2;
Eltseq(s) eq Eltseq(s2);

