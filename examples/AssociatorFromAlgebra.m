O := OctonionAlgebra(GF(1223),-1,-1,-1);
t := AssociatorTensor(O);
t;
<Random(O),Random(O),Random(O)> @ t eq O!0;


a := Random(O); 
b := Random(O); 
<a,a,b> @ t eq O!0;
IsAlternating(t);

