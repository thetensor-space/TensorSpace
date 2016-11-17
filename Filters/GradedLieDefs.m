declare attributes AlgLie: GradedInfo;

/* 
  Description of GradedInfo record:
    HomogeneousComponents. . . . . . A list of vector spaces corresponding the the homogeneous components.
    HomogeneousIndices . . . . . . . A list of indices in the same order as the list of homogeneous components.
    Projections. . . . . . . . . . . A list of projections onto the various homogeneous componenets.
    Bimaps . . . . . . . . . . . . . A list of the nontrivial bimaps given by the graded product of the Lie algebra.
    BimapIndices . . . . . . . . . . A list of the pair of indices for each of the bimaps in the same order as Bimaps.
    StructureConstants . . . . . . . The structure constants of the Lie algebra.
*/

intrinsic LieAlgebra( F::Flt ) -> AlgLie, Map
{Returns the associated graded Lie algebra to F.}
  if assigned F`Lie_Alg and assigned F`Lie_Func then
    return F`Lie_Alg, F`Lie_Func;
  end if;
  G := F`Object;
  require Type(G) eq GrpPC : "Filter must be for a pc group."; // current working assumption
  require IsSeries(F) : "Filter must be a series."; // current working assumption
  fact := Factorisation( #G );
  require #fact eq 1 : "Group must be a p-group."; // current working assumption
  p := fact[1][1];
  n := fact[1][2];
  require forall{ i : i in [1..Length(F)] | forall{ h : h in Generators(Image(F)[i]) | h^p in Image(F)[i+1] } and 
    forall{ [h,k] : h in Generators(Image(F)[i]), k in Generators(Image(F)[i]) | (h,k) in Image(F)[i+1] } } : 
    "Factors must be elementary abelian.";
  require F`Max_Inds eq true : "Filter must have a maximum index for all subgroups."; // current working assumption

  // initialize things
  B := BoundaryFilter(F);  
  SC := [ KMatrixSpace( GF(p), n, n )!0 : i in [1..n] ]; // structure constants
  bimaps := [* *]; // all nontrivial bimaps
  bimap_inds := []; // all nontrivial bimap indices
  gens := []; // ordered generating set for G
  spaces := [* *]; // homogeneous spaces
  maps := [* *]; // projections onto the homogeneous spaces

  // compute the quotients and save for later.
  for i in [1..Length(F)] do
    s := F`Indices[i];
    U,f := GModule( G, s @ F, s @ B );
    Append(~spaces, U);
    Append(~maps, f);
    gens cat:= [ b @@ f : b in Basis(U) ];
  end for;

  // construct the structure constants for the associated Lie algebra, and construct the bimaps along the way.
  for i in [1..Length(F)] do
    for j in [i..Length(F)] do
      s := F`Indices[i];
      t := F`Indices[j];
      u := [ s[k] + t[k] : k in [1..#s] ];
      U := spaces[i];
      f := maps[i];
      V := spaces[j];
      g := maps[j];

      // avoid the case where W is 0-dimensional.
      if u in Prune(F`Indices) then
        k := Index(F`Indices,u);
        W := spaces[k];
        h := maps[k];

        // construct structure constants for Ls x Lt >-> Ls+t.
        sc := [ KMatrixSpace( GF(p), Dimension(U), Dimension(V) )!0 : l in [1..Dimension(W)] ];
        for x in [1..Dimension(U)] do
          for y in [1..Dimension(V)] do
            vec := Coordinates( W, ( U.x @@ f, V.y @@ g ) @ h );
            for z in [1..Dimension(W)] do
              sc[z][x][y] +:= vec[z];
            end for;
          end for;
        end for;
        if s eq t then
          Bi := Tensor( sc, 2, 1, TensorCategory([1,1,1],{{0},{1,2}}) );
        else
          Bi := Tensor( sc, 2, 1 );
        end if;
        Append(~bimaps, Bi);
        Append(~bimap_inds, <s,t>);

        // insert these structure constants into the global structure constants.
        d1 := &+([ Dimension(spaces[l]) : l in [1..i-1] ] cat [0]);
        d2 := &+([ Dimension(spaces[l]) : l in [1..j-1] ] cat [0]);
        d3 := &+([ Dimension(spaces[l]) : l in [1..k-1] ] cat [0]);
        for l in [1..Dimension(W)] do
          InsertBlock( ~(SC[d3+l]), sc[l], d1+1, d2+1 );
          if i ne j then
            InsertBlock( ~(SC[d3+l]), -Transpose(sc[l]), d2+1, d1+1 );
          end if;
        end for;

      end if;
    end for;
  end for;

  // construct the Lie algebra with the graded information recorded.
  L := LieAlgebra< GF(p), n | [ [ [ SC[k][i][j] : k in [1..n] ] : j in [1..n] ] : i in [1..n] ] >;
  rf := recformat< HomogeneousComponents : List, HomogeneousIndices : SeqEnum, Projections : List, Bimaps : List, BimapIndices : SeqEnum, StructureConstants : SeqEnum >;
  homo_comp := [* VectorSpace( GF(p), Dimension(X) ) : X in spaces *];
  homo_ind := Prune(F`Indices);
  dims := [0] cat [ &+[ Dimension(spaces[i]) : i in [1..j-1] ] : j in [2..#spaces] ];
  projs := [* hom< L -> homo_comp[j] | [ <L.i, homo_comp[j]!0> : i in [1..dims[j]] ] cat 
              [ <L.i, homo_comp[j].(i-dims[j])> : i in [dims[j]+1..dims[j]+Dimension(homo_comp[j])] ] cat
              [ <L.i, homo_comp[j]!0> : i in [dims[j]+Dimension(homo_comp[j])+1..n] ] > : j in [1..#homo_comp] *];
  R := rec< rf | HomogeneousComponents := homo_comp, 
                 HomogeneousIndices := homo_ind,
                 Projections := projs,
                 Bimaps := bimaps,
                 BimapIndices := bimap_inds,
                 StructureConstants := SC >;
  L`GradedInfo := R;

  // construct a functor mapping the group to the Lie algebra and vice versa.
  M := Matrix( GF(p), [ Eltseq(g) : g in gens ] );
  V := KSpace( GF(p), n );
  phi := map< G -> L | x :-> L!(V!(Eltseq(x))*M^-1), y :-> G!(V!(Eltseq(y))*M) >; 
  F`Lie_Alg := L;
  F`Lie_Func := phi;
  return L,phi;
end intrinsic;

intrinsic GradedProducts( L::AlgLie ) -> List
{Returns all the nontrivial bimaps from the graded product on L.}
  require assigned L`GradedInfo : "Lie algebra must come from a filter.";
  bimaps := L`GradedInfo`Bimaps;
  inds := L`GradedInfo`BimapIndices;  
  return [* < inds[i], bimaps[i] > : i in [1..#inds] *];
end intrinsic;

intrinsic FilterToTensor( F::Flt, s::SeqEnum, t::SeqEnum ) -> TenSpcElt 
{Returns the bimap of the associated Lie algebra from Ls x Lt >-> Ls+t.
If any factor is 0-dimensional, it returns false.}  
  require F`Max_Inds : "Filter must have maximal indices for every subgroup."; // current working assumption
  require #s eq #t : "Indices have unequal length.";
  require F`Domain eq #s : "Indices not in domain of filter.";
  u := [ s[i] + t[i] : i in [1..#s] ];
  if not [s,t,u] subset F`Indices then
    return false;
  end if;
  L := LieAlgebra(F);
  if <s,t> notin L`GradedInfo`BimapIndices then
    return false;
  else
    return L`GradedInfo`Bimaps[Index(L`GradedInfo`BimapIndices,<s,t>)];
  end if;  
end intrinsic;

intrinsic FilterToTensor( F::Flt, s::RngIntElt, t::RngIntElt ) -> TenSpcElt
{Returns the bimap of the associated Lie algebra from Ls x Lt >-> Ls+t.
If any factor is 0-dimensional, it returns false.}  
  require F`Max_Inds : "Filter must have maximal indices for every subgroup."; // current working assumption
  require F`Domain eq 1 : "Indices not in domain of filter.";
  return FilterToTensor(F,[s],[t]);
end intrinsic;

intrinsic HomogeneousComponents( L::AlgLie ) -> List, List
{Returns the list of homogeneous components of L and a list of projections from L onto its components.}
  require assigned L`GradedInfo : "Lie algebra must come from a filter.";
  return L`GradedInfo`HomogeneousComponents,L`GradedInfo`Projections;
end intrinsic;

intrinsic StructureConstants( L::AlgLie ) -> SeqEnum
{Returns the structure constants of L.}
  require assigned L`GradedInfo : "Lie algebra must come from a filter.";
  return L`GradedInfo`StructureConstants;
end intrinsic;

__E := function(MS,i,j)
  n := Nrows(MS.1);
  m := Ncols(MS.1);
  return MS.(m*(i-1)+j);
end function;

intrinsic GradedDerivationAlgebra( L::AlgLie ) -> AlgMatLie
{Returns the graded derivation algebra from the given graded Lie algebra.}
  require assigned L`GradedInfo : "Cannot recognize the grading.";
  T := Tensor(L);
  ChangeTensorCategory(~T,HomotopismCategory(2));
  D2 := Induce(DerivationAlgebra(T),2);
  D1 := Induce(DerivationAlgebra(T),1);
  dims := [Dimension(D1),Dimension(D2)];
  D := [*D1,D2*][Index(dims,Maximum(dims))];
  H := L`GradedInfo`HomogeneousComponents;
  MS := KMatrixSpace( BaseRing(L), Degree(L), Degree(L) );
  B := [];
  ipos := 1;
  jpos := 1;
  for h in H do
    d := Dimension(h);
    B cat:= [ __E(MS,ipos+i,jpos+j) : i in [0..d-1], j in [0..Degree(L)-jpos] ];
    ipos +:= d;
    jpos +:= d;
  end for;
  B_D := [ Matrix(X) : X in Basis(D) ];
  B_I := Basis( sub< MS | B > meet sub< MS | B_D > );
  GD := sub< MatrixLieAlgebra( BaseRing(L), Degree(L) ) | B_I >;
  return GD;
end intrinsic;
