t := RandomTensor(GF(2), [5,4,3,2,1]);
t;

G := Sym({0..4});
g := G![2, 3, 4, 0, 1];
g;

s := Shuffle(t, g);
s;

