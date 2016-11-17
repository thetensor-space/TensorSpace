T := RandomTensor(GF(7),[5,4,3]);
F := Frame(T);

I := [* hom< F[j] -> F[j] | [< F[j].i,F[j].i > :\
  i in [1..Dimension(F[j])]] > : j in [1..3] *];
H := Homotopism(T,T,I);

Image(H);
Kernel(H);


M := [* RandomMatrix(GF(7),i,i) : i in [5,4,3] *];
G := Homotopism(T,T,M);
G;

G*G;

Cat := TensorCategory([1,-1,1],{{0},{1},{2}});
G := Homotopism(T,T,M,Cat);
G;

Image(G);

Kernel(G);

