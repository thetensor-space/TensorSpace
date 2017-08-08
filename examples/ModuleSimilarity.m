R := MatrixAlgebra(GF(3),2);     
A := sub<R| [R!1, R![0,1,2,0]]>;
B := sub<R| [R!1, R![1,1,2,1]]>;
A eq B;
M := RModule(A); // A 1-dim. GF(9) vector space.
N := RModule(B); // A 1-dim. GF(9) vector space.
IsIsomorphic(M,N);
MinimalPolynomial(A.2);
MinimalPolynomial(B.2);


IsSimilar(M,N);


p := RandomIrreduciblePolynomial(GF(101), 10); 
q := RandomIrreduciblePolynomial(GF(101), 10); 
X := CompanionMatrix(p);
Y := CompanionMatrix(q);
A := sub<Parent(X)|[X]>;	// Finite field of size 101^10
B := sub<Parent(Y)|[Y]>;	// Finite field of size 101^10
M := RModule(A);		// 1-dim vector space over A.
N := RModule(B);		// 1-dim vector space over B.
IsIsomorphic(M,N);		// Not isomorphic as A and B are distinct.
cyc, f := IsSimilar(M,N);	// But similar as A is isomorphic to B.
// f conjugates A into B
forall { a : a in Generators (A) | f * a * f^-1 in B };
// and f is a semilinear transform M->N.
forall{ i : i in [1..Ngens (M)] | forall { j : j in [1..Ngens (A)] | \
(Vector(M.i * A.j) * f) eq (Vector(M.i)*f)*(f^(-1)*A.j*f) } };


M := RandomMatrix(GF(9), 100, 100);
A := sub< Parent(M) | [ M^(Random(50)) : i in [1..10]] >;
Ngens(A);
assert IsCyclic(A);
