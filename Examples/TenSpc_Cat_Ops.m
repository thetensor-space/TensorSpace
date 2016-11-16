T := KTensorSpace(GF(2),[4,4,2]);
T;

L := [ T.i : i in [1..Ngens(T)] | IsEven(i) ];
S := SubtensorSpace(T, L);
S;
SystemOfForms(Random(S));

Q := T/S;
Q;
SystemOfForms(Random(Q));

SystemOfForms(Q![1 : i in [1..32]]);

