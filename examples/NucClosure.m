H := ClassicalSylow(GL(3,125), 5);
t := pCentralTensor(H);
t;


C := Centroid(t);
C;
s := TensorOverCentroid(t);
s;


NucleusClosure(Parent(s), s, 2, 1);

NucleusClosure(Parent(t), t, 2, 1);

