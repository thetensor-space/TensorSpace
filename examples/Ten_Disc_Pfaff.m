J := Matrix(GF(7),[[0,1],[-1,0]]);
J;
M := [ InsertBlock(ZeroMatrix(GF(7),4,4),J,i,i) 
      : i in [1..3] ]; 
M;
T := Tensor(M,2,1);
T;
Discriminant(T);
Pfaffian(T);

