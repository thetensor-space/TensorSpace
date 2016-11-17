T := RandomTensor(GF(3),[10,10,4]);
V := Domain(T)[1];
V.1*T*V.2;
A := HeisenbergAlgebra(T);
A;
A.1*A.2;

L := HeisenbergLieAlgebra(T);
L.1*L.2;
aT := AlternatingTensor(T);
V.1*aT*V.2;

G := HeisenbergGroup(T);  // Runs through p-Quotient
(G.2,G.1);  // Defining word for 1st gen in Frattini

