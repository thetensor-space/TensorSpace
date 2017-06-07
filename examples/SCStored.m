sl20 := MatrixLieAlgebra("A19", GF(3));
M4 := MatrixAlgebra(GF(3), 4);
Prod := func< x | Matrix(x[1])*DiagonalJoin(<x[2] : i in [1..5]>) >;
T := Tensor([* sl20, M4 *], MatrixAlgebra(GF(3), 20), Prod);
T;


time sc := StructureConstants(T);

time sc := StructureConstants(T);

