T := KTensorSpace(Rationals(), [5,5,5]);
A := VectorSpace(Rationals(), 5);
t := T!0;
for i in [1..5] do
  Assign(~t, [i,i,i], 1);
end for;
t;
SystemOfForms(t);


s := Ideal(t, [A.1, A.2, A.3]);
s;


r := Subtensor(t, [A.1, A.2], [A.2, A.3]);
IsIdeal(t, r);

