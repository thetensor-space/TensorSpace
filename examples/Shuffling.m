T := RandomTensor(GF(2), [5,4,3,2,1]);
T;

G := Sym({0..4});
g := G![2, 3, 4, 0, 1];
g;

S := Shuffle(T, g);
S;

