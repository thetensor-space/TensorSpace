P := ClassicalSylow(GL(3, 3^5), 3);
P := PCPresentation(UnipotentMatrixGroup(P));
Z := Center(P);
N := sub< Z | [Random(Z) : i in [1..3]] >;
G := P/N;


A := ClassicalSylow(GL(3, 9), 3);
B := ClassicalSylow(GL(3, 27), 3);
A := PCPresentation(UnipotentMatrixGroup(A));
B := PCPresentation(UnipotentMatrixGroup(B));
Q, inc := DirectProduct(A, B);
ZA := Center(A);
ZB := Center(B);
gens := [(ZA.i@inc[1])*(ZB.i@inc[2])^-1 : i in [1..2]] \
    cat [ZB.3@inc[2]];
M := sub< Q | gens >;
H := Q/M;


t := pCentralTensor(G);
t;

s := pCentralTensor(H);
s;


R<x,y> := PolynomialRing(GF(3), 2);
f := R!Pfaffian(t);
g := R!Pfaffian(s);
f;
g;
Factorization(f), Factorization(g);

