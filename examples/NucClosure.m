H := ClassicalSylow( GL(3,125), 5 ); // Heisenberg group
T := pCentralTensor(H,5,1,1);
T;

C := Centroid(T);
C;

S := TensorOverCentroid(T);
S;

TS := Parent(S);
N := NucleusClosure(TS,S,2,1);
N;


NT := NucleusClosure(Parent(T),T,2,1);
NT;

