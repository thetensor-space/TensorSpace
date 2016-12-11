G := ClassicalSylow(GL(3,1024),2);
P := PCPresentation(UnipotentMatrixGroup(G));
T := pCentralTensor(P,1,1);
T;
TC := TensorOverCentroid(T);
TC;
IsAlternating(TC);

