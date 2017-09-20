/* 
    Copyright 2016, 2017, Joshua Maglione, James B. Wilson.
    Distributed under GNU GPLv3.
*/


/*
  This file contains utilities for the user and functions to construct algebraic
  objects from tensors.
*/

import "../Tensor/TensorData.m" : __GetSlice, __GetForms;
import "../GlobalVars.m" : __FRAME;


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

__GetRepresentation := function( T )
  sc := T`CoordImages;
  U := T`Domain[1];
  V := T`Domain[2];
  W := T`Codomain;
  a := Dimension(U);
  b := Dimension(V);
  c := Dimension(W);
  K := BaseRing(U);
  r := Dimension(Radical(T, 1));
  d := (a ne b) select 1+a+b+c else 1+a+r+c;
  I := IdentityMatrix(K, d);

  if T`Cat`Repeats eq {{2,1},{0}} and IsAlternating(T) then
    gens := [ InsertBlock(InsertBlock(I, Matrix(K, 1, a, Eltseq(U.i)), 1, 2), __GetForms(__GetSlice(sc, [a, b, c], [{i},{1..b},{1..c}]), [1, b, c], 1, 0)[1], d-b-c+1, d-c+1) : i in [1..a] ];
  else
    gens_U := [ InsertBlock(I, Matrix(K, 1, a, Eltseq(u)), 1, 2) : u in Basis(U) ];
    gens_V := [ InsertBlock(I, X, 2, d-c+1) : X in __GetForms(sc, [a, b, c], 2, 0) ];
    gens := gens_U cat gens_V;
  end if;
  gens cat:= [ InsertBlock(I, Matrix(K, 1, c, Eltseq(w)), 1, d-c+1) : w in Basis(W) ]; // in case not full
  gens cat:= [ InsertBlock(I, Matrix(K, 1, 1, [1]), 1, a+1+i) : i in [1..r] ];
  G := sub< GL(d, K) | gens >;
  return G;
end function;

/*
Input a matrix M
returns [  0   M ]
        [ -M^t 0 ].
*/
__Scharlau := function( M )
	k := Parent(M[1][1]);
	return MatrixAlgebra(k,Nrows(M)+Ncols(M))!VerticalJoin( HorizontalJoin( ZeroMatrix( k, Nrows(M), Nrows(M) ), M ), HorizontalJoin( -Transpose(M), ZeroMatrix( k, Ncols(M), Ncols(M) ) ) );
end function;

// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
intrinsic HeisenbergGroup( t::TenSpcElt ) -> GrpMat
{Returns the matrix group of class 2 from the given tensor t.}
  require t`Valence eq 3 : "Tensor must have valence 3.";
  try
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;
  return __GetRepresentation(t);
end intrinsic;

//intrinsic HeisenbergGroupPC( t::TenSpcElt ) -> GrpPC
//{Returns the pc-group of class 2 and exponent p from the given tensor t over a finite field.}
//  require t`Valence eq 3 : "Tensor must have valence 3.";
//  try
//    _ := Eltseq(t);
//  catch err
//    error "Cannot compute structure constants.";
//  end try;
//  Forms := SystemOfForms(t);
//  K := BaseRing(Forms[1]);
//  require ISA(Type(K), FldFin) : "Base field must be finite.";
//  p := Characteristic(K);

//  if #K gt p then
//    Forms := __WriteOverPrimeField(Forms);
//  end if;
//  if t`Cat`Repeats eq {{2,1},{0}} and IsAlternating(t) then
//    require Nrows(Forms[1]) + #Forms le 256 : "Cannot handle groups larger than p^256.";
//  else
//    require Nrows(Forms[1]) + Ncols(Forms[1]) + #Forms le 256 : "Cannot handle groups larger than p^256.";
//    Forms := [ __Scharlau(X) : X in Forms ];
//  end if;

//  d := Nrows(Forms[1]);
//  e := #Forms;
//  F := FreeGroup( d+e );
//  powers := [ F.i^p = 1 : i in [1..d+e] ];
//  commutators := [];
//  for i in [1..d] do
//    for j in [i+1..d] do
//      commutators cat:= [ F.j^F.i = F.j * &*[ F.(d+k)^(Integers()!(Forms[k][i][j])) : k in [1..e] ] ];
//    end for;
//  end for;
//  Q := quo< F | powers cat commutators >;
//  P := pQuotient( Q, p, 2 : Exponent := p );
//  return P;
//end intrinsic;

intrinsic HeisenbergGroupPC( t::TenSpcElt ) -> GrpPC
{Returns the pc-group of class 2 and exponent p from the given tensor t over a finite field.}
  require t`Valence eq 3 : "Tensor must have valence 3.";
  try
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;
  Forms := SystemOfForms(t);
  K := BaseRing(Forms[1]);
  require ISA(Type(K), FldFin) : "Base field must be finite.";
  p := Characteristic(K);

  if #K gt p then
    Forms := __WriteOverPrimeField(Forms);
  end if;
  if not (t`Cat`Repeats eq {{2,1},{0}} and IsAlternating(t)) then
    Forms := [ __Scharlau(X) : X in Forms ];
  end if;

  d := Nrows(Forms[1]);
  e := #Forms;
  F := FreeGroup( d+e );
  powers := [ F.i^p = 1 : i in [1..d+e] ];
  commutators := [];
  for i in [1..d] do
    for j in [i+1..d] do
      commutators cat:= [ F.j^F.i = F.j * &*[ F.(d+k)^(Integers()!(Forms[k][i][j])) : k in [1..e] ] ];
    end for;
  end for;
  P := quo< GrpPC : F | powers cat commutators >;
  return P;
end intrinsic;

intrinsic HeisenbergAlgebra( t::TenSpcElt ) -> AlgGen
{Returns the algebra whose product is given by the tensor.}
  require t`Valence eq 3 : "Tensor must have valence 3.";
  try
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;
  K := BaseRing(t);
  fuse := t`Cat`Repeats;
  dims := [ Dimension(X) : X in __FRAME(t) ];
  if fuse eq {{0,1,2}} then // nonassociative 
    sc := Eltseq(t);
    n := dims[1];
  elif fuse eq {{0},{1,2}} then // nilpotent
    Forms := SystemOfForms(t);
    Forms := [ ZeroMatrix(K, dims[1], dims[1]) : i in [1..dims[1]] ] cat Forms;
    Forms := [ DiagonalJoin(X, ZeroMatrix(K, dims[3], dims[3])) : X in Forms ];
    sc := Eltseq(Tensor(Forms, 2, 1));
    n := dims[1] + dims[3];
  else // generic
    n := &+(dims);
    Forms := [ ZeroMatrix(K, n, n) : i in [1..n] ];
    OldForms := SystemOfForms(t);
    for i in [1..dims[3]] do
      Forms[n-dims[3]+i] := InsertBlock(Forms[n-dims[3]+i], OldForms[i], 1, dims[1]+1);
    end for;
    sc := Eltseq(Tensor(Forms, 2, 1));
  end if;
  A := Algebra< K, n | sc >;
  return A;
end intrinsic;

intrinsic HeisenbergLieAlgebra( t::TenSpcElt ) -> AlgLie
{Returns the Lie algebra whose Lie bracket is given by the tensor.}
  require t`Valence eq 3 : "Tensor must have valence 3.";
  try
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;
  K := BaseRing(t);
  fuse := t`Cat`Repeats;
  dims := [ Dimension(X) : X in __FRAME(t) ];
  if fuse eq {{2,1},{0}} and IsAlternating(t) then
    n := dims[1]+dims[3]; 
    Forms := [ ZeroMatrix(K, n, n) : i in [1..n] ];
    OldForms := SystemOfForms(t);
    for i in [1..dims[3]] do
      Forms[n-dims[3]+i] := InsertBlock(Forms[n-dims[3]+i], OldForms[i], 1, 1);
    end for;
    sc := Eltseq(Tensor(Forms, 2, 1));
  else
    n := &+(dims);
    Forms := [ ZeroMatrix(K, n, n) : i in [1..n] ];
    OldForms := SystemOfForms(t);
    for i in [1..dims[3]] do
      Forms[n-dims[3]+i] := InsertBlock(Forms[n-dims[3]+i], OldForms[i], 1, dims[1]+1);
      Forms[n-dims[3]+i] := InsertBlock(Forms[n-dims[3]+i], -Transpose(OldForms[i]), dims[1]+1, 1);
    end for;
    sc := Eltseq(Tensor(Forms, 2, 1));
  end if;
  L := LieAlgebra< K, n | sc >;
  return L;
end intrinsic;

intrinsic Induce( X::GrpMat, a::RngIntElt ) -> GrpMat, Map
{Given a group of matrices associated to a tensor, returns the restriction of the object onto the ath coordinate and a projection.}
  require assigned X`DerivedFrom : "Cannot find the associated tensor.";
  require Type(X`DerivedFrom[1]) eq TenSpcElt : "Cannot recognize associated tensor.";
  require X`DerivedFrom[1]`Valence-a in X`DerivedFrom[2] : "No restriction found.";
  return __GetInduction(X,a);
end intrinsic;

intrinsic Induce( X::AlgMat, a::RngIntElt ) -> AlgMat, Map
{Given an algebra of matrices associated to a tensor, returns the restriction of the object onto the ath coordinate and a projection.}
  require assigned X`DerivedFrom : "Cannot find the associated tensor.";
  require Type(X`DerivedFrom[1]) eq TenSpcElt : "Cannot recognize associated tensor.";
  require X`DerivedFrom[1]`Valence-a in X`DerivedFrom[2] : "No restriction found.";
  return __GetInduction(X,a);
end intrinsic;

intrinsic Induce( X::AlgMatLie, a::RngIntElt ) -> AlgMatLie, Map
{Given a Lie algebra of matrices associated to a tensor, returns the restriction of the object onto the ath coordinate and a projection.}
  require assigned X`DerivedFrom : "Cannot find the associated tensor.";
  require Type(X`DerivedFrom[1]) eq TenSpcElt : "Cannot recognize associated tensor.";
  require X`DerivedFrom[1]`Valence-a in X`DerivedFrom[2] : "No restriction found.";
  return __GetInduction(X,a);
end intrinsic;

intrinsic DerivationAlgebra( A::Alg ) -> AlgMatLie
{Returns the derivation algebra of A.}
  if Dimension(A) eq 0 then
    return MatrixLieAlgebra(BaseRing(A), 0);
  end if;
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
  if Dimension(A) eq 0 then
    return MatrixAlgebra(BaseRing(A), 0);
  end if;
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
  if Dimension(A) eq 0 then
    return MatrixAlgebra(BaseRing(A), 0);
  end if;
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
  if Dimension(A) eq 0 then
    return MatrixAlgebra(BaseRing(A), 0);
  end if;
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
  if Dimension(A) eq 0 then
    return MatrixAlgebra(BaseRing(A), 0);
  end if;
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
  if Dimension(A) eq 0 then
    return A;
  end if;
  if Type(BaseRing(A)) in {FldRe,FldCom} then 
    "Warning: answers known to be incorrect for the Real and Complex fields.";
  end if;
  B := CommutatorTensor(A);
  R := Radical(B);
  C := R[1] meet R[2];
  S := sub< A | [ c @@ B`Coerce[1] : c in Basis(C) ] >;
  return S;
end intrinsic;


// ------------------------------------------------------------------------------
//                                    Printing
// ------------------------------------------------------------------------------

intrinsic Sprint( C::TenCat ) -> MonStgElt
{Returns the string that can be executed in Magma to construct the tensor category.}
  return "TensorCategory(" * Sprint(Arrows(C), "Magma") * ", " * Sprint(C`Repeats, "Magma") * ")";
end intrinsic;

intrinsic Sprint( t::TenSpcElt ) -> MonStgElt
{Returns the string that can be executed in Magma to construct the tensor t.}
  try
    sc := Sprint(Eltseq(t), "Magma");
  catch err
    return Sprint(t, "Magma");
  end try;
  rng := Sprint(BaseRing(t), "Magma");
  dim := Sprint([Dimension(X) : X in __FRAME(t)], "Magma");
  ctg := Sprint(t`Cat);

  return "Tensor(" * rng * ", " * dim * ", " * sc * ", " * ctg * ")"; 
end intrinsic;

intrinsic Sprint( T::TenSpc ) -> MonStgElt
{Returns the string that can be executed in Magma to construct the tensor space T.}
  frm := "[*";
  for X in __FRAME(T) do
    frm *:= Sprint(X, "Magma")*", ";
  end for;
  frm := frm[1..#frm-2] * "*]";
  ctg := Sprint(T`Cat);
  tenspc := "TensorSpace(" * frm * ", " * ctg * ")";
  
  if Dimension(T) eq &*[Dimension(X) : X in __FRAME(T)] then
    return tenspc;
  end if;

  bas := "[";
  if Dimension(T) eq 0 then
    bas *:= "]";
  else
    for t in Basis(T) do
      bas *:= Sprint(t) * ", ";
    end for;
    bas := bas[1..#bas-2] * "]";
  end if;

  return "sub< " * tenspc * " | " * bas * " >";
end intrinsic;
