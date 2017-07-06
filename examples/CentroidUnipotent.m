U := ClassicalSylow(GL(3, 2^10), 2);
U.3;
G := PCPresentation(UnipotentMatrixGroup(U));
#G eq 2^30;
t := pCentralTensor(G);
t;


C := Centroid(t);
C;
IsCyclic(C) and IsSimple(C);
s := TensorOverCentroid(t);
s;

