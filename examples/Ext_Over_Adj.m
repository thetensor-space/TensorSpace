//p := 317;
//e := 4;
//H := ClassicalSylow( GL(3,p^e), p );
//U := UnipotentMatrixGroup(H);
//P := PCPresentation(U);
//Z := Center(P);

//N := sub< P | >;
//while #N lt p^2 do
//  N := sub< P | Random(Z), N >;
//end while;

//G := P/N;
//G;

//T := pCentralTensor(G,1,1);
//T;

//A := AdjointAlgebra(T);
//Dimension(A);
//star := Star(A);

//V := Domain(T)[1];
//E := ExteriorCotensorSpace(V,2);
//E;


//L := [];
//for E_gen in Generators(E) do
//  F := SystemOfForms(E_gen)[1];
//  for X in Basis(A) do
//    L cat:= [E!Eltseq(X*F - F*Transpose(X@star))];
//  end for;
//end for;

//S := SubTensorSpace(E,L);
//S;

//Q := E/S;
//Q;


