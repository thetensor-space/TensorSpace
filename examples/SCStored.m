sl20 := MatrixLieAlgebra("A19", GF(3));
M4 := MatrixAlgebra(GF(3), 4);
Prod := func< x | Matrix(x[1])*DiagonalJoin(<x[2] : i in [1..5]>) >;
t := Tensor([* sl20, M4 *], MatrixAlgebra(GF(3), 20), Prod);
t;


time sc := StructureConstants(t);

time sc := StructureConstants(t);

