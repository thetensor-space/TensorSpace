V := VectorSpace(GF(3), 3);
T := TensorSpace([V, V, V]);
t := T.1+T.14+T.27;
P := PermutationMatrix(GF(3), [2,1,3]);
f := hom< V -> V | [<V.1, V.2>, <V.2, V.1>, <V.3, V.3>] >;
H := Homotopism(t, t, [*f, f, f*]);
H;


H2 := Homotopism(t, t, [*P, f, P*]);
H2;

