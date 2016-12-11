

__find_albert_params := function( p, e )
	// 
	K := GF(p^e);
	x := PrimitiveElement(K);
	params := [];
	for s in [1..(e-1)] do
		if (Order( x^(p^GCD(s,e)-1)) mod 2) eq 0 then continue; end if;
		for t in [1..(e-1)] do
			if (Order( x^(p^GCD(t,e)-1)) mod 2) eq 1 then 
				Append(~params, [s,t] );
			end if;
		end for;
	end for;
	return params;
end function;

__AlbertSemifield := function( p, e, s, t, a )
	MS := KMatrixSpace( GF(p), e,e );
	X := CompanionMatrix( RandomIrreduciblePolynomial( GF(p), e ) );

	basis := [ MS!X^i : i in [0..(e-1)] ];
	V := KMatrixSpaceWithBasis( basis );
	str_const := [ GF(p)!0 : i in [1..e^3] ];
	// work out X^i*X^j = X^i.X^j-a (X^i)^(p^s) (X^j)^(p^t)
	for i in [0..(e-1)] do
		A := X^i;
		for j in [0..(e-1)] do
			B := X^j;
			C := MS!(A*B - (a)* A^(p^s) * B^(p^t));
			v := Coordinates( V, C );
			for k in [1..e] do
				str_const[e^2*(i)+e*j+k] := v[k];
			end for;
		end for;
	end for;
	return Algebra< GF(p), e | str_const >;
end function;

intrinsic AlbertSemifield( q::RngIntElt, d::RngIntElt, r::[RngIntElt] ) -> AlgGen
{An Albert semifield with given parameters.}
	f := Factorization(q);
	require #f eq 1 : "Order must be a power of a prime.";
	p := f[1][2];
	e := f[1][2];

	s := r[1];
	t := r[2];
	require not (s*t) eq 0 : "Field automorphisms cannot be trivial.";


	MS := KMatrixSpace( GF(p), e,e );
	X := CompanionMatrix( RandomIrreduciblePolynomial( GF(p), e ) );
require (Order( X^(p^GCD(s,e)-1)) mod 2) eq 1 
		and (Order( X^(p^GCD(t,e)-1)) mod 2) eq 1 : "No Albert semifield with given parameters.";
	return __AlbertSemifield( p, d, r[1], r[2], t[3] );
end intrinsic;

intrinsic RandomAlbertSemifield(q::RngIntElt) -> AlgGen
{A random Albert semifield of the given order.}
	f := Factorization(q);
	require #f eq 1 : "Order must be a power of a prime.";
	p := f[1][2];
	e := f[1][2];
	params := __find_albert_params( p, e );
	param := Random( params );
	return __AlbertSemifield( p,e, param[1], param[2], -1);
end intrinsic;
