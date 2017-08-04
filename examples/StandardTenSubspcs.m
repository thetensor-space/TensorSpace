K := GF(3);
T := KTensorSpace(K, [4, 4, 4]);
T;


Alt := AlternatingSpace(T);
Alt;
t := Random(Alt);
t;
IsAlternating(t);


S := SymmetricSpace(Alt);
S;

