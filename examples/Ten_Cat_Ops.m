T := RandomTensor(GF(5),[4,4,2]);
T;

F := Frame(T);
L := [* F[1]![1,1,1,0], F[2]![0,0,0,1], F[3]![0,0] *];
S := Subtensor(T,L);
S;

IsSubtensor(T,S);



I := Ideal(T,S);
I;

IsIdeal(T,I);



T/I;

