CT := KCotensorSpace(GF(2),[ i : i in [5..7] ]);
CT;

CT.1;


Cat := CotensorCategory([1,0,-1],{{1},{2},{3}});
Fr := [ VectorSpace(GF(8),4) : i in [1..3] ];
CT := CotensorSpace( Fr, Cat );
CT;

TensorCategory(CT);
