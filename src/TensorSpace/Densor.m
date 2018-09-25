/* 
    Copyright 2016, 2017, Joshua Maglione, James B. Wilson.
    Distributed under GNU GPLv3.
*/


/*
  This file contains the constructor for the densor subspace of a tensor.
*/


import "TensorSpc.m" : __GetTensorSpace;
import "../GlobalVars.m" : __SANITY_CHECK;
import "../Util/Util.m" : __GetInduction;

// Given a Lie subalgebra of operators Delta_Lie and dims [a,b,c], compute the tensors t (flat arrays) such that Delta_Lie is a subset of Der(t).
__GetDensorTensors := function( Delta_Lie, dims )
  /* Assumption:
   *   dims = [a, b, c]
   *   T : K^a x K^b >-> K^c
   *   #Ngens(Delta_Lie) = d
   * Solves abc linear equations with abcd variables. 
   */

  Delta := [D : D in Generators(Delta_Lie)];
  K := BaseRing(Delta_Lie);
  d := #Delta;
  a := dims[1];
  b := dims[2];
  c := dims[3];

  // Temporary fix. I think the better fix is to simplify the computation below if there is a nontrivial repeat partition.
  // For now, we just increase the size of Delta.
  if #Delta_Lie`DerivedFrom`Tensor`Cat`Repeats lt 3 then
    Delta_projs := [Induce(Delta_Lie, a) : a in Reverse([0..2])];
    Delta := [DiagonalJoin(<X @ Delta_projs[i] : i in [1..3]>) : X in Delta];
  end if;

  vprint eMAGma, 1 : "Setting linear system: " cat IntegerToString(a*b*c) cat " by " cat IntegerToString(a*b*c*d);

  offset := [1,a+1,a+b+1];
  blocks := [* [ ExtractBlock(X,offset[i],offset[i],dims[i],dims[i]) : X in Delta ] : i in [1..3] *];
  Z := ZeroMatrix(K, a*b*c, a*b*c*d);
  Y := ZeroMatrix(K, a*b*c*d, a*b*c);
  X := ZeroMatrix(K, a*b*c*d, a*b*c);
  
  // Z Block
  jpos := 1;
  for i in [1..d] do
    ipos := 1;
    for j in [1..a*b] do
      InsertBlock(~Z,blocks[3][i],ipos,jpos);
      ipos +:= c;
      jpos +:= c;
    end for;
  end for;

  // Y Block
  ipos := 1;
  for i in [1..d] do
    jpos := 1;
    for j in [1..a] do
      Yblock := [];
      for k in [1..b] do
        vec := &cat[ [x] cat [0 : i in [1..c-1]] : x in Eltseq(blocks[2][i][k]) ];
        for l in [1..c] do
          Append(~Yblock,vec);
          Remove(~vec,#vec);  
          vec := [0] cat vec;
        end for;      
      end for;
      InsertBlock(~Y,Matrix(K,Yblock),ipos,jpos);
      ipos +:= b*c;
      jpos +:= b*c;
    end for;
  end for;

  // X Block
  ipos := 1;
  for i in [1..d] do
    for j in [1..a] do
      vec := &cat[[x] cat [0 : i in [1..b*c-1]] : x in Eltseq(blocks[1][i][j])];
      for k in [1..b*c] do
        InsertBlock(~X,Matrix(K,1,a*b*c,vec),ipos,1);
        Remove(~vec,#vec);
        vec := [0] cat vec;
        ipos +:= 1;
      end for;
    end for;
  end for;

  M := Transpose(X+Y)-Z;
  delete X, Y, Z;

  vprint eMAGma, 1 : "Solving linear system: " cat IntegerToString(a*b*c) cat " by " cat IntegerToString(a*b*c*d);

  N := NullspaceMatrix(M);
  return N;
end function;

// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
intrinsic DerivationClosure( T::TenSpc, Delta::[Mtrx] ) -> TenSpc
{Returns the derivation closure of the tensor space with the given operators Delta.}
  require T`Valence eq 3 : "Tensor space must have valence 3.";
  require BaseRing(T) eq BaseRing(Delta[1]) : "Base rings are incompatible.";

  // remove redundant dims if coords are fused.
  ess_dims := [ Dimension(X) : X in T`Frame ];
  for P in [P : P in T`Cat`Repeats | #P gt 1] do
    m := Maximum(P);
    for p in P diff {m} do
      ess_dims[T`Valence - p] := 0;
    end for;
  end for;
  ess_dims := [d : d in ess_dims | d ne 0];
  dims := [ Dimension(X) : X in T`Frame ];

  matched_fused := Nrows(Delta[1]) eq &+ess_dims and Ncols(Delta[1]) eq &+ess_dims;
  matched_not_fused := Nrows(Delta[1]) eq &+dims and Ncols(Delta[1]) eq &+dims;

  require matched_fused or matched_not_fused : "Incompatible operators.";

  // Package the Delta into a Lie algebra 
  Delta_Lie := sub< MatrixLieAlgebra(BaseRing(T), Nrows(Delta[1])) | Delta >;
  DerivedFrom(~Delta_Lie, T!0, [0..2] : Fused := matched_fused); // Really just need the tensor category info

  N := __GetDensorTensors(Delta_Lie, dims);
  S := __GetTensorSpace(T`Ring, T`Frame, T`Cat);
  S`Mod := sub< T`Mod | [ T`Mod!N[i] : i in [1..Nrows(N)] ] >;

  if __SANITY_CHECK and Dimension(S) gt 0 then
    printf "Running sanity check (DerivationClosure)\n";
    assert forall{ i : i in [1..10] | Delta subset DerivationAlgebra(Random(S)) };
  end if;

  return S;
end intrinsic;

intrinsic DerivationClosure( T::TenSpc, Delta::[AlgMatLie] ) -> TenSpc
{Returns the derivation closure of the tensor space with the given operators Delta.}
  return DerivationClosure(T, [ Matrix(X) : X in Delta ]);
end intrinsic;

intrinsic DerivationClosure( T::TenSpc, Delta::AlgMatLie ) -> TenSpc
{Returns the derivation closure of the tensor space with the given operators Delta.}
  return DerivationClosure(T, Basis(Delta));
end intrinsic;

intrinsic DerivationClosure( T::TenSpc, Delta::AlgMat ) -> TenSpc
{Returns the derivation closure of the tensor space with the given operators Delta.}
  return DerivationClosure(T, Basis(Delta));
end intrinsic;

intrinsic DerivationClosure( T::TenSpc, Delta::ModMatFld ) -> TenSpc
{Returns the derivation closure of the tensor space with the given operators Delta.}
  return DerivationClosure(T, Basis(Delta));
end intrinsic;

intrinsic DerivationClosure( T::TenSpc, t::TenSpcElt ) -> TenSpc
{Returns the derivation closure of the tensor space with operators given by the derivation algebra of t.}
  return DerivationClosure(T, Basis(DerivationAlgebra(t)));
end intrinsic;

intrinsic UniversalDensorSubspace( t::TenSpcElt ) -> TenSpc
{Returns the universal densor subsapce of t in the universal tensor space of t, with operators given by the derivation algebra of t.}
  if not assigned t`Densor then
    densor := DerivationClosure(Parent(t), Basis(DerivationAlgebra(t)));
    t`Densor := densor;
  end if;
  return t`Densor;
end intrinsic;

intrinsic NucleusClosure( T::TenSpc, Delta::[Mtrx], a::RngIntElt, b::RngIntElt ) -> TenSpc
{Returns the nucleus closure of the tensor space with the given operators Delta acting on Ua and Ub.}
  require T`Valence eq 3 : "Tensor space must have valence 3.";
  K := BaseRing(T);
  require K eq BaseRing(Delta[1]) : "Base rings are incompatible.";

  dims := [ Dimension(X) : X in T`Frame ];
  a := 3-a;
  b := 3-b;
  c := Random({1,2,3} diff {a,b}); // only one elt...
  require (&+(dims[[a,b]]) eq Nrows(Delta[1])) and (Nrows(Delta[1]) eq Ncols(Delta[1])) : "Incompatible operators.";

  blocks := [* [ ExtractBlock( X, 1, 1, dims[a], dims[a] ) : X in Delta ], [ ExtractBlock( -Transpose(X), dims[a]+1, dims[a]+1, dims[b], dims[b] ) : X in Delta ], [ ZeroMatrix(K,dims[c],dims[c]) : i in [1..#Delta] ] *];
  perm := [1,2,3];
  temp := [a,b,c];
  ParallelSort(~temp,~perm);
  M := [DiagonalJoin( < blocks[perm[i]][j] : i in [1..3] > ) : j in [1..#Delta]];
  Delta_Lie := sub<MatrixLieAlgebra(K, &+dims) | M>;
  DerivedFrom(~Delta_Lie, T!0, [0..2] : Fused := false); // important not to fuse! 
  pi2 := Induce(Delta_Lie, 2);
  pi1 := Induce(Delta_Lie, 1);
  V := Domain(T!0)[1];
  t := Random(T);

  N := __GetDensorTensors(Delta_Lie, dims);
  S := __GetTensorSpace( T`Ring, T`Frame, T`Cat );
  S`Mod := sub< T`Mod | [ T`Mod!N[i] : i in [1..Nrows(N)] ] >;
  if __SANITY_CHECK and Dimension(S) gt 0 then
    printf "Running sanity check (NucleusClosure)\n";
    assert forall{ i : i in [1..10] | Delta subset Nucleus(Random(S), 3-a, 3-b) };
  end if;
  return S;
end intrinsic;

intrinsic NucleusClosure( T::TenSpc, Delta::AlgMat, a::RngIntElt, b::RngIntElt ) -> TenSpc
{Returns the nucleus closure of the tensor space with the given operators Delta acting on Ua and Ub.}
  return NucleusClosure(T, Basis(Delta), a, b);
end intrinsic;

intrinsic NucleusClosure( T::TenSpc, Delta::ModMatFld, a::RngIntElt, b::RngIntElt ) -> TenSpc
{Returns the nucleus closure of the tensor space with the given operators Delta acting on Ua and Ub.}
  return NucleusClosure(T, Basis(Delta), a, b);
end intrinsic;

intrinsic NucleusClosure( T::TenSpc, t::TenSpcElt, a::RngIntElt, b::RngIntElt ) -> TenSpc
{Returns the nucleus closure of the tensor space with the ab-nucleus of the given tensor t.}
  return NucleusClosure(T, Basis(Nucleus(t, a, b)), a, b);
end intrinsic;
