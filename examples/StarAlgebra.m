A := OctonionAlgebra(Rationals(),-1,-1,-1);
IsStarAlgebra(A);

s := Star(A);
A.1; // A.1 is the mult. id.
A.1 @ s; 

A.2;
A.2 @ s;

