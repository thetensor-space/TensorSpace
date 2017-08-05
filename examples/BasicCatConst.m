C := TensorCategory([1,0,-1], {{0},{1},{2}});
C;
IsCovariant(C);

arrows := map< {1..5} -> {1} | x :-> 1 >;
C := CotensorCategory(arrows, {{1..5}});
C;
IsContravariant(C);

