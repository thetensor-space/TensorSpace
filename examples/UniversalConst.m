T := KTensorSpace(Rationals(), [6,6,2]);
S := AlternatingSpace(T);
S;
IsAlternating(S);


U := UniversalTensorSpace(S);
U;
U eq T;

