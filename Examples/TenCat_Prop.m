C1 := TensorCategory([1,1,-1,1],{{0,3},{1},{2}});
C1;

A := map< {0..3} -> {-1,0,1} | x :-> 1 >;
C2 := TensorCategory(A,{{0..3}});
C2;

C1 eq C2;
RepeatPartition(C2);
Valence(C2);
Arrows(C2);

