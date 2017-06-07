sc := [ 0 : i in [1..8] ];
sc[1] := 1;
Tensor([2, 2, 2], sc);


K := GF(64);
T := Tensor(K, [2, 2, 2], sc);
T;

Image(T);


StructureConstants(T);

<[1, 0], [K.1^3, 0]> @ T;

<[K.1^29, 1], [0, K.1^2]> @ T;

