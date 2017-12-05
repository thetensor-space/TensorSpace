
jprod := function( x )
	X := x[1];//Matrix(n,n, Eltseq(x[1]));
	Y := x[2]; //Matrix(n,n, Eltseq(x[2]));
	return (1/2)*Parent(X)!(X*Y+Y*X);//Eltseq( X*Y+Y*X );
end function;

SimpleJordanAlgebraTypeA := function( K, n )
	MS := KMatrixSpace(K,n,n);
	f := func< x | 1/2*(x[1]*x[2]+x[2]*x[1]) >;
	return Tensor( [MS, MS,MS], f );
end function;

SimpleJordanAlgebraTypeB := function( K, m )
	n := 2*m+1;
	MS := KMatrixSpace(K,n,n);
	V := sub<  MS | [ X+Transpose(X) : X in Basis(MS)] >;
	f := func< x | 1/2*(x[1]*x[2]+x[2]*x[1]) >;
	return Tensor( [V, V, V], f );
end function;

my_trace := function(x)
	sum := BaseRing(x)!0; 
	for i in [1..Nrows(x)] do
		sum +:= x[i][i]; 
	end for; 
	return sum;
end function;

TracelessJordanAlgebraA  := function( K, n )
	MS := KMatrixSpace(K,n,n);
	I := MS!IdentityMatrix(K,n);
	V := sub<MS | [X-(1/n)*my_trace(X)*I : X in Basis(MS)]>;
	f := func< x | (x[1]*x[2]+x[2]*x[1])-(1/n)*my_trace(x[1]*x[2]+x[2]*x[1])*I >;
	return Tensor( [V, V, V], f );
end function;


TracelessJordanAlgebraB  := function( K, m )
	n := 2*m+1;
	MS := KMatrixSpace(K,n,n);  // Don't use MatrixAlgebra
	I := MS!IdentityMatrix(K,n);
	V := sub<MS | [(X+Transpose(X))-(1/n)*my_trace(X+Transpose(X))*I : X in Basis(MS)]>; // subspace not subalgebra
	f := func< x | (x[1]*x[2]+x[2]*x[1])-(1/n)*my_trace(x[1]*x[2]+x[2]*x[1])*I >;
	return Tensor( [V, V, V], f );
end function;

