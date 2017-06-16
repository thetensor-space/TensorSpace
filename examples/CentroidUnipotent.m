U := ClassicalSylow(GL(3, 2^10), 2);
U.3;
G := PCPresentation(UnipotentMatrixGroup(U));
#G eq 2^30;
T := pCentralTensor(G);
T;


C := Centroid(T);
C;
IsCyclic(C) and IsSimple(C);
S := TensorOverCentroid(T);
S;

