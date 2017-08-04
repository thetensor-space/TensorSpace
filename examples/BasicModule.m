K := GF(8);
T := KTensorSpace(K, [3,5,7]);
T;


Dimension(T);
#Basis(T);
T.100 in Basis(T);
T.100;
#T eq 8^(3*5*7);

