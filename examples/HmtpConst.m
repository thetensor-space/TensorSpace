TS := KTensorSpace(GF(4),[2,3,4]);
T := Random(TS);
S := Random(TS);
M := [* Random(KMatrixSpace(GF(4),i,i)) : i in [2..4] *];
H := Homotopism(T,S,M);
H;


M[2] := map< Frame(TS)[2] -> Frame(TS)[2] | x :-> x >;
H2 := Homotopism(T,S,M);
H2;

