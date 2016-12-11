P := ClassicalSylow(SL(3,125),5);
Q := PCGroup(P); // Loose track of GF (125).
Q;
T := pCentralTensor(Q,1,1);
F := Centroid(T); // Recover GF (125)
Dimension(F);
IsSimple(F);
IsCommutative(F);
