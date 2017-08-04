V := VectorSpace(GF(5), 6);
T := ExteriorCotensorSpace(V, 2);
T;


t := Random(T);
t;
SystemOfForms(t);
IsAlternating(t);


s := AsTensor(T);
s;
IsAlternating(s);

