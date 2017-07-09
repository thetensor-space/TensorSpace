K := GF(5);
T := TensorSpace(K, 4, 3, 2);
T;
S := KTensorSpace(K, [4, 4, 4, 4, 4, 1]);
S;


TensorCategory(S); // default category
TensorCategory(T); 
S eq T;

