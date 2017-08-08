V := VectorSpace(Rationals(), 6);
T := KTensorSpace(Rationals(), [6, 6, 1]);
t := T.2-T.7+T.16-T.21+T.30-T.35;
t;

u := V.2+2*V.3-V.5;
L := map< V -> V | x :-> x + (x*t*u)[1]*u >;
L;
M := Matrix(6, 6, [V.i @ L : i in [1..6]]);
M;


H := Homotopism(t, t, [*L, L, IdentityMatrix(Rationals(), 1)*]);
H;


H2 := H*H;
H2;
M2 := Matrix(6, 6, [V.i @ H2.2 : i in [1..6]]);
M2;
M^2 eq M2;

