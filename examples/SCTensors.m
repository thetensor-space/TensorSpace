sc := [ 0 : i in [1..8] ];
sc[1] := 1;
Tensor([2, 2, 2], sc);


K := GF(64);
t := Tensor(K, [2, 2, 2], sc);
t;

Image(t);


StructureConstants(t);

<[1, 0], [K.1^3, 0]> @ t;

<[K.1^29, 1], [0, K.1^2]> @ t;

