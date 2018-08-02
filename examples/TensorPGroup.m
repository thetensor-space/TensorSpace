P := ClassicalSylow(SL(3,125),5);
Q := PCGroup(P); // Lose track of GF(125).
Q;
t := pCentralTensor(Q);
t;


F := Centroid(t); // Recover GF(125)
Dimension(F);
IsSimple(F);
IsCommutative(F);
s := TensorOverCentroid(t);
s;

