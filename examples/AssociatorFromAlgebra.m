O := OctonionAlgebra(GF(1223),-1,-1,-1);
T := AssociatorTensor(O);
T;
<Random(O),Random(O),Random(O)> @ T eq O!0;


a := Random(O); 
b := Random(O); 
<a,a,b> @ T eq O!0;
IsAlternating(T);

