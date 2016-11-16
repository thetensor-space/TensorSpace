T := RandomTensor(GF(3),[3,4,5,6]);
T;
Valence(T);

BaseRing(T);

Frame(T);

Domain(T);

Codomain(T);

Parent(T); // Universal tensor space

TensorCategory(T);

Cat := TensorCategory([-1,-1,1,1],{{i} : i in [0..3]});
ChangeTensorCategory(~T, Cat);
TensorCategory(T);

