/* 
    Copyright 2016, 2017, Joshua Maglione, James B. Wilson.
    Distributed under GNU GPLv3.
*/


/*
  This file contains utilities for the user and functions to construct algebraic
  objects from tensors.
*/

import "../Tensor/TensorBasic.m" : __GetSlice, __GetForms;


__GetInduction := function( X, i )
  t := X`DerivedFrom[1];
  v := t`Valence;
//  j := v-i+1;
  j := v-i; // corrected after change in valence rules.
  gens := [ g : g in Generators(X) ];
  grp := Type(X) eq GrpMat;
  lie := Type(X) eq AlgMatLie;
  K := BaseRing(t);
  spaces := Frame(t);
  d := Dimension(spaces[j]);
  s := &+([Dimension(spaces[k]) : k in [ x : x in X`DerivedFrom[2] | x lt j ]] cat [1]);
  blocks := { ExtractBlock(g,s,s,d,d) : g in gens };
  if grp then
    if GL(d,K)!1 in blocks then
      Exclude(~blocks,GL(d,K)!1);
    end if;
    Y := sub< Generic(GL(d,K)) | blocks >;
  else
    if lie then
      if MatrixLieAlgebra(K,d)!0 in blocks then
        Exclude(~blocks,MatrixLieAlgebra(K,d)!0);
      end if;
      Y := sub< MatrixLieAlgebra(K,d) | blocks >;
    else
      if MatrixAlgebra(K,d)!0 in blocks then
        Exclude(~blocks,MatrixAlgebra(K,d)!0);
      end if;
      Y := sub< MatrixAlgebra(K,d) | blocks >;
    end if;
  end if;
  proj := map< X -> Y | x :-> Y!ExtractBlock(x,s,s,d,d) >;
  return Y, proj;
end function;

__WriteOverPrimeField := function( Forms )
  M := Tensor(Forms,2,1);
  K := BaseRing(M);
  k := GF(Characteristic(K));
  e := Round(Log(#k, #K));
  D_old := M`Domain;
  D_new := [*KSpace( k, Dimension(D)*e ) : D in D_old*];
  C_old := M`Codomain;
  C_new := KSpace( k, Dimension(M`Codomain)*e );
  maps_D := [ map< D_new[i] -> D_old[i] | 
    x :-> D_old[i]![ K![ Coordinates(D_new[i],x)[j] : j in [(k-1)*e+1..k*e] ] : k in [1..Dimension(D_old[i])] ],
    y :-> D_new[i]!(&cat[ &cat[ Eltseq( s ) : s in Coordinates(D_old[i],y) ] ]) > : i in [1..#D_old] ];
  map_C := map< C_old -> C_new | 
    x :-> C_new!(&cat[ &cat[ Eltseq( s ) : s in Coordinates(C_old,x) ] ]),
    y :-> C_old![ K![ Coordinates(C_new,y)[j] : j in [(k-1)*e+1..k*e] ] : k in [1..Dimension(C_old)] ] >;
  F := function(x)
    return (< x[i] @ maps_D[i] : i in [1..#x] > @ M) @ map_C;
  end function;
  N := Tensor( D_new, C_new, F );
  assert forall{ b : b in CartesianProduct( < [ c*K.1^i : i in [0..e-1], c in Basis(D) ] : D in D_old > ) | 
    (b @ M) @ map_C eq < b[i] @@ maps_D[i] : i in [1..#b] > @ N };
  return SystemOfForms(N);
end function;

__GetRepresentation := function( T : UseAlt := true )
  sc := T`CoordImages;
  U := T`Domain[1];
  V := T`Domain[2];
  W := T`Codomain;
  a := Dimension(U);
  b := Dimension(V);
  c := Dimension(W);
  K := BaseRing(U);
  d := (a ne b) select 1+a+b+c else 1+a+c;
  Z := ZeroMatrix(K, d, d);
  I := IdentityMatrix(K, d);

  if UseAlt then
    gens := [ I + InsertBlock(InsertBlock(Z, Matrix(K, 1, a, Eltseq(U.i)), 1, 2), __GetForms(__GetSlice(sc, [a, b, c], [{i},{1..b},{1..c}]), [1, b, c], 1, 0)[1], d-b-c+1, d-c+1) : i in [1..a] ];
  else
    gens_U := [ I + InsertBlock(Z, Matrix(K, 1, a, Eltseq(u)), 1, 2) : u in Basis(U) ];
    gens_V := [ I + InsertBlock(Z, X, 2, d-c+1) : X in __GetForms(sc, [a, b, c], 2, 0) ];
    gens := gens_U cat gens_V;
  end if;
  G := sub< GL(d, K) | gens >;
  return G;
end function;

/*
Input a matrix M
returns [  0   M ]
        [ -M^t 0 ].
*/
__Scharlau := function( M );
	k := Parent(M[1][1]);
	return MatrixAlgebra(k,Nrows(M)+Ncols(M))!VerticalJoin( HorizontalJoin( ZeroMatrix( k, Nrows(M), Nrows(M) ), M ), HorizontalJoin( -Transpose(M), ZeroMatrix( k, Ncols(M), Ncols(M) ) ) );
end function;

// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
intrinsic HeisenbergGroup( B::TenSpcElt : UseAlt := true ) -> GrpMat
{Returns the matrix group of class 2 from the given tensor B.}
  require B`Valence eq 3 : "Tensor must have valence 3.";
  try
    _ := Eltseq(B);
  catch err
    error "Cannot compute structure constants.";
  end try;
  return __GetRepresentation(B : UseAlt := UseAlt and IsAlternating(B));
end intrinsic;

intrinsic HeisenbergGroupPC( B::TenSpcElt : UseAlt := true ) -> GrpPC
{Returns the pc-group of class 2 and exponent p from the given tensor B over a finite field.}
  require B`Valence eq 3 : "Tensor must have valence 3.";
  try
    _ := Eltseq(B);
  catch err
    error "Cannot compute structure constants.";
  end try;
  Forms := SystemOfForms(B);
  K := BaseRing(Forms[1]);
  require ISA(Type(K), FldFin) : "Base field must be finite.";
  p := Characteristic(K);

  if #K gt p then
    Forms := __WriteOverPrimeField(Forms);
  end if;
  if UseAlt and IsAlternating(B) then
    require Nrows(Forms[1]) + #Forms le 256 : "Cannot handle groups larger than p^256.";
  else
    require Nrows(Forms[1]) + Ncols(Forms[1]) + #Forms le 256 : "Cannot handle groups larger than p^256.";
    Forms := [ __Scharlau(X) : X in Forms ];
  end if;

  d := Nrows(Forms[1]);
  e := #Forms;
  F := FreeGroup( d+e );
  powers := [ F.i^p = 1 : i in [1..d] ];
  commutators := [];
  for i in [1..d] do
    for j in [i+1..d] do
      commutators cat:= [ F.j^F.i = F.j * &*[ F.(d+k)^(Integers()!(Forms[k][i][j])) : k in [1..e] ] ];
    end for;
  end for;
  Q := quo< F | powers cat commutators >;
  P := pQuotient( Q, p, 2 : Exponent := p );
  return P;
end intrinsic;

intrinsic HeisenbergAlgebra( B::TenSpcElt ) -> AlgGen
{Returns the algebra whose product is given by the tensor.}
  require B`Valence eq 3 : "Tensor must have valence 3.";
  try
    _ := Eltseq(B);
  catch err
    error "Cannot compute structure constants.";
  end try;
  K := BaseRing(B);
  if Dimension(B`Domain[1]) ne Dimension(B`Domain[2]) then
    Forms := SystemOfForms(B);
    c := Dimension(B`Domain[1]);
    d := Dimension(B`Domain[2]);
    Forms := [ InsertBlock(ZeroMatrix(K,c+d,c+d),f,1,c+1) : f in Forms ];
    B := Tensor(Forms,2,1);
  end if;
  if Dimension(B`Domain[1]) ne Dimension(B`Codomain) then
    Forms := SystemOfForms(B);
    d := Dimension(B`Domain[1]);
    e := Dimension(B`Codomain);
    Forms := [ ZeroMatrix(K,d+e,d+e) : i in [1..d] ] cat [ DiagonalJoin(f,ZeroMatrix(K,e,e)) : f in Forms ];
    B := Tensor(Forms,2,1);
  end if;
  A := Algebra< K, Dimension(B`Domain[1]) | Eltseq(B) >;
  return A;
end intrinsic;

intrinsic HeisenbergLieAlgebra( B::TenSpcElt ) -> AlgLie
{Returns the Lie algebra whose Lie bracket is given by the tensor.}
  require B`Valence eq 3 : "Tensor must have valence 3.";
  try
    _ := Eltseq(B);
  catch err
    error "Cannot compute structure constants.";
  end try;
  K := BaseRing(B);
  B := AlternatingTensor(B);
  Forms := SystemOfForms(B);
  if Dimension(B`Domain[1]) ne Dimension(B`Codomain) then
    d := Dimension(B`Domain[1]);
    e := Dimension(B`Codomain);
    Forms := [ ZeroMatrix(K,d+e,d+e) : i in [1..d] ] cat [ DiagonalJoin(f,ZeroMatrix(K,e,e)) : f in Forms ];
    B := Tensor(Forms,2,1);
  end if;
  L := LieAlgebra< K, Dimension(Domain(B)[1]) | Eltseq(B) >;
  return L;
end intrinsic;

intrinsic Induce( X::GrpMat, i::RngIntElt ) -> GrpMat, Map
{Given a group of matrices associated to a tensor, returns the restriction of the object onto the ith space and a projection.}
  require assigned X`DerivedFrom : "Cannot find the associated tensor.";
  require Type(X`DerivedFrom[1]) eq TenSpcElt : "Cannot recognize associated tensor.";
  require X`DerivedFrom[1]`Valence-i in X`DerivedFrom[2] : "No restriction found.";
  return __GetInduction(X,i);
end intrinsic;

intrinsic Induce( X::AlgMat, i::RngIntElt ) -> AlgMat, Map
{Given an algebra of matrices associated to a tensor, returns the restriction of the object onto the ith space and a projection.}
  require assigned X`DerivedFrom : "Cannot find the associated tensor.";
  require Type(X`DerivedFrom[1]) eq TenSpcElt : "Cannot recognize associated tensor.";
  require X`DerivedFrom[1]`Valence-i in X`DerivedFrom[2] : "No restriction found.";
  return __GetInduction(X,i);
end intrinsic;

intrinsic Induce( X::AlgMatLie, i::RngIntElt ) -> AlgMatLie, Map
{Given a Lie algebra of matrices associated to a tensor, returns the restriction of the object onto the ith space and a projection.}
  require assigned X`DerivedFrom : "Cannot find the associated tensor.";
  require Type(X`DerivedFrom[1]) eq TenSpcElt : "Cannot recognize associated tensor.";
  require X`DerivedFrom[1]`Valence-i in X`DerivedFrom[2] : "No restriction found.";
  return __GetInduction(X,i);
end intrinsic;

intrinsic DerivationAlgebra( A::Alg ) -> AlgMatLie
{Returns the derivation algebra of A.}
  if Type(BaseRing(A)) in {FldRe,FldCom} then 
    "Warning: answers known to be incorrect for the Real and Complex fields.";
  end if;
  B := Tensor(A);
  D := DerivationAlgebra(B);
  Der := Induce(D,2);
  return Der;
end intrinsic;

intrinsic Centroid( A::Alg ) -> AlgMat
{Returns the centroid of A.}
  if Type(BaseRing(A)) in {FldRe,FldCom} then 
    "Warning: answers known to be incorrect for the Real and Complex fields.";
  end if;
  B := Tensor(A);
  C := Centroid(B);
  Cent := Induce(C,2);
  return Cent;
end intrinsic;

intrinsic LeftNucleus( A::Alg ) -> AlgMat
{Returns the left nucleus of A.}
  if Type(BaseRing(A)) in {FldRe,FldCom} then 
    "Warning: answers known to be incorrect for the Real and Complex fields.";
  end if;
  K := BaseRing(A);
  d := Dimension(A);
  B := Tensor(A);
  N := Induce(Nucleus(B,2,0),2);
  bas := Basis(sub<KMatrixSpace(K,d,d)|[ Transpose(X) : X in Basis(N) ]> meet sub<KMatrixSpace(K,d,d)|AsMatrices(B,2,0)>);
  L := sub< MatrixAlgebra(K,d) | bas >;
  return L;
end intrinsic;

intrinsic RightNucleus( A::Alg ) -> AlgMat
{Returns the right nucleus of A.}
  if Type(BaseRing(A)) in {FldRe,FldCom} then 
    "Warning: answers known to be incorrect for the Real and Complex fields.";
  end if;
  K := BaseRing(A);
  d := Dimension(A);
  B := Tensor(A);
  N := Induce(Nucleus(B,1,0),1);
  bas := Basis(sub<KMatrixSpace(K,d,d)|Basis(N)> meet sub<KMatrixSpace(K,d,d)|AsMatrices(B,2,0)>);
  R := sub< MatrixAlgebra(K,d) | bas >;
  return R;
end intrinsic;

intrinsic MidNucleus( A::Alg ) -> AlgMat
{Returns the mid nucleus of A.}
  if Type(BaseRing(A)) in {FldRe,FldCom} then 
    "Warning: answers known to be incorrect for the Real and Complex fields.";
  end if;
  K := BaseRing(A);
  d := Dimension(A);
  B := Tensor(A);
  N := Induce(Nucleus(B,2,1),2);
  bas := Basis(sub<KMatrixSpace(K,d,d)|Basis(N)> meet sub<KMatrixSpace(K,d,d)|AsMatrices(B,2,0)>);
  M := sub< MatrixAlgebra(K,d) | bas >;
  return M;
end intrinsic;

intrinsic Center( A::Alg ) -> Alg
{Returns the center of A.}
  if Type(BaseRing(A)) in {FldRe,FldCom} then 
    "Warning: answers known to be incorrect for the Real and Complex fields.";
  end if;
  B := CommutatorTensor(A);
  R := Radical(B);
  C := R[1] meet R[2];
  S := sub< A | [ c @@ B`Coerce[1] : c in Basis(C) ] >;
  return S;
end intrinsic;
