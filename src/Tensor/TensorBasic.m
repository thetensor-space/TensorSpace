/* 
    Copyright 2016, 2017, Joshua Maglione, James B. Wilson.
    Distributed under GNU GPLv3.
*/


/*
  This file contains basic functions for tensors (TenSpcElt).
*/


import "../GlobalVars.m" : __LIST, __SANITY_CHECK, __FRAME;
import "Tensor.m" : __GetTensor, __TensorOnVectorSpaces;
import "../TensorCategory/Hom.m" : __GetHomotopism;
import "../TensorCategory/TensorCat.m" : __TensorCatSanity;

__HasBasis := function( X )
  try 
    B := Basis(X);
  catch e
    return false;
  end try;
  return true;
end function;

// A function which takes a multimap M, and a list D of objects in the domain of M.
// Returns a list of spaces in the domain, provided the objects are in the domain of M.
__GenerateDomain := function( M, D )
  dom := M`Domain;
  n := #dom;
  list := [* *];
  i := 1;
  while i le n do
    if __HasBasis(D[i]) then
      // subspace
      B := Basis(D[i]);
      if forall{ b : b in B | IsCoercible(dom[i],b) } then
        Append(~list, sub< dom[i] | [ dom[i]!b : b in B ] >);
      else
        return false;
      end if;
    else
      // generators
      if Type(D[i]) in {SeqEnum,SetEnum,SetIndx,List} then
        if forall{ b : b in D[i] | IsCoercible(dom[i],b) } then
          Append(~list, sub< dom[i] | [ dom[i]!b : b in D[i] ] >);
        else
          return false;
        end if;
      else
        if IsCoercible(dom[i],D[i]) then
          Append(~list, sub< dom[i] | D[i] >);
        else
          return false;
        end if;
      end if;
    end if;
    i +:= 1;
  end while;
  return list;
end function;

// A function which takes a multimap M, and anything for C.
// Returns a list of generators for C in the codomain, provided it is coercible.
// Otherwise, returns false.
__GenerateCodomain := function( M, C )
  cod := M`Codomain;
  if __HasBasis(C) then
    //subspace
    B := Basis(C);
    if forall{ b : b in B | IsCoercible(cod,b) } then
      S := sub< cod | [ cod!b : b in B ] >;
    else
      return false;
    end if;
  else
    //generators
    if Type(C) in {SeqEnum,SetEnum,SetIndx,List} then
      if forall{ b : b in C | IsCoercible(cod,b) } then
        S := sub< cod | [ cod!b : b in C ] >;
      else
        return false;
      end if;
    else
      if IsCoercible(cod,C) then
        S := sub< cod | C >;
      else
        return false;
      end if;
    end if;
  end if;
  return S;
end function;

// t: tensor, C: tensor category
__CopyTensorWithCat := function( t, C )
  F := function(x)
    return x @ t;
  end function;
  s := __GetTensor( t`Domain, t`Codomain, F : Cat := C );
  if assigned t`CoordImages then
    s`CoordImages := t`CoordImages;
  end if;
  return s;
end function;

// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
intrinsic Domain( t::TenSpcElt ) -> List
{Returns the domain of t.}
  return t`Domain;
end intrinsic;

intrinsic Codomain( t::TenSpcElt ) -> .
{Returns the codomain of t.}
  return t`Codomain;
end intrinsic;

intrinsic Valence( t::TenSpcElt ) -> RngIntElt
{Returns the valence of t.}  
  return t`Valence;
end intrinsic;

intrinsic Frame( t::TenSpcElt ) -> List
{Returns the frame of t.}
  if t`Cat`Contra then
    return t`Domain;
  end if;
	return t`Domain cat [* t`Codomain *];
end intrinsic;

intrinsic TensorCategory( t::TenSpcElt ) -> TenCat
{Returns the tensor category of t.}
  return t`Cat;
end intrinsic;

intrinsic IsContravariant( t::TenSpcElt ) -> BoolElt
{Decides if the tensor is contravariant.}
  return t`Cat`Contra;
end intrinsic;

intrinsic IsCovariant( t::TenSpcElt ) -> BoolElt
{Decides if the tensor is covariant.}
  return not t`Cat`Contra;
end intrinsic;

intrinsic ChangeTensorCategory( t::TenSpcElt, C::TenCat ) -> TenSpcElt
{Returns the given tensor in the given category.}
  require t`Cat`Contra eq C`Contra : "Both must be co- or contravariant.";
  require C`Valence eq t`Valence : "Valence does not match.";
  passed, err := __TensorCatSanity( __FRAME(t), C );
  require passed : err;
  return __CopyTensorWithCat(t,C);
end intrinsic;

intrinsic ChangeTensorCategory( ~t::TenSpcElt, C::TenCat )
{Returns the given tensor in the given category.}
  require t`Cat`Contra eq C`Contra : "Both must be co- or contravariant.";
  require C`Valence eq t`Valence : "Valence does not match.";
  passed, err := __TensorCatSanity( __FRAME(t), C );
  require passed : err;
  t := __CopyTensorWithCat(t,C);
end intrinsic;

intrinsic BaseRing( t::TenSpcElt ) -> Rng
{For the tensor t, where each Vi is a R-bimodule, returns R. If Vi is not an R-bimodule, then returns false.}
  D := t`Domain;
  R := BaseRing( D[1] ); 
  try
    require forall{ X : X in t`Domain cat [* t`Codomain *] | BaseRing(X) eq R } : "Tensor does not have a common base ring.";
  catch err
    error "No covering ring for modules in frame.";
  end try;
  return R;
end intrinsic;

intrinsic BaseField( t::TenSpcElt ) -> Fld
{For the tensor t, where each Vi is a F-vector space, returns F. If Vi is not an F-vector space, then returns false.}
  K := BaseRing(t);
  require ISA( Type(K), Fld ) : "Base ring is not a field.";
  return K;
end intrinsic;

intrinsic Image( t::TenSpcElt ) -> ModTupRng
{Returns the image of t as a subspace of the codomain.}
  if assigned t`Image then
    return t`Image;
  end if;

  try
    sc := Eltseq(t);
  catch err
    gens := [ g : g in CartesianProduct( < Basis(X) : X in t`Domain > ) ];
    i := 1;
    S := sub< t`Codomain | >;
    while i le #gens and Dimension(S) lt Dimension(t`Codomain) do
      S := sub< t`Codomain | S, gens[i] >;
      i +:= 1;
    end while;
    S := sub< S | Basis(S) >;// Magma work-around : remove superfluous generators
    t`Image := S;
    return S;
  end try;

  d := Dimension(t`Codomain);
  if d eq 0 then
    t`Image := t`Codomain;
    return t`Codomain;
  end if;
  i := 1;
  total := #sc div d;
  S := sub< t`Codomain | >;
  while i le total and Dimension(S) lt Dimension(t`Codomain) do
    S := sub< t`Codomain | S, t`Codomain!sc[(i-1)*d+1..i*d] >;
    i +:= 1;
  end while;
  S := sub< S | Basis(S) >;// Magma work-around : remove superfluous generators
  t`Image := S;
  return S;
end intrinsic;

intrinsic NondegenerateTensor( t::TenSpcElt ) -> TenSpcElt, Hmtp
{Returns the associated nondegenerate tensor of t along with a homotopism.}
  if assigned t`Nondegenerate then
    return t`Nondegenerate[1], t`Nondegenerate[2];
  end if;
  if exists{ X : X in t`Domain cat [* t`Codomain *] | Type(X) ne ModTupFld } then
    passed, t, H2, err := __TensorOnVectorSpaces(t);
    require passed : err;
  end if;
  R := BaseRing(t);
  D := t`Domain;
  Rad := Radical(t);
  dom := [* *];
  proj := [* *];
  for i in [1..#D] do
    Q,pi := D[i]/Rad[i];
    Append(~dom,Q);
    Append(~proj,pi);
  end for;
  Append(~proj,hom< t`Codomain -> t`Codomain | [ <b,b> : b in Basis(t`Codomain) ] >);
  
  F := function(x)
    return < x[i] @@ proj[i] : i in [1..#x] > @ t;
  end function;

  s := __GetTensor( dom, t`Codomain, F : Cat := t`Cat );
  s`Radicals := [* sub< dom[i] | > : i in [1..#dom] *];
  if assigned t`Coerce then
    s`Coerce := [* t`Coerce[i] * proj[i] : i in [1..#proj] *];
  end if;
  H := __GetHomotopism( t, s, proj : Cat := HomotopismCategory(t`Valence : Contravariant := t`Cat`Contra) );
  if assigned H2 then
    H := H2*H;
  end if;
  t`Nondegenerate := < s, H >;
  return s, H;
end intrinsic;

intrinsic IsNondegenerate( t::TenSpcElt ) -> BoolElt
{Decides if t is nondegenerate.}
  Rad := Radical(t);
  return forall{ R : R in Rad | R eq sub< R | R!0 > };
end intrinsic;

intrinsic FullyNondegenerateTensor( t::TenSpcElt ) -> TenSpcElt, Hmtp
{Returns the fully nondegenerate tensor of t.}
  if assigned t`FullyNondeg then
    return t`FullyNondeg[1], t`FullyNondeg[2];
  end if;
  s, H := NondegenerateTensor(t);
  if t`Cat`Contra then
    return s, H;
  end if;
  I := Image(s);
  inc := hom< I -> s`Codomain | [ <b,b> : b in Basis(I) ] >;
  F := function(x)
    return x @ s;
  end function;
  full_s := __GetTensor( s`Domain, I, F : Cat := t`Cat );
  H := __GetHomotopism(t, full_s, H`Maps[1..#H`Maps-1] cat [* H`Maps[#H`Maps] * inc *] : Cat := CohomotopismCategory(t`Valence));
  t`FullyNondeg := <full_s, H>;
  return full_s, H;
end intrinsic;

intrinsic IsFullyNondegenerate( t::TenSpcElt ) -> BoolElt
{Decides if t is fully nondegenerate.}
  return IsNondegenerate(t) and (Codomain(t) eq Image(t));
end intrinsic;

intrinsic AssociatedForm( t::TenSpcElt ) -> TenSpcElt
{If t : Un x ... x U1 >-> U0, returns the associated form s : Un x ... x U0 >-> K.}
  if exists{ X : X in Frame(t) | Type(X) ne ModTupFld } then
    passed, t, _, err := __TensorOnVectorSpaces(t);
    require passed : err;
  end if;
  K := BaseRing(t);
  require ISA(Type(K),Fld) : "Base ring must be a field.";
  D := __FRAME(t);
  C := VectorSpace(K,1);
  F := function(x)
    y := < x[i] : i in [1..#x-1] >;
    return C![DotProduct(y @ t, x[#x])];
  end function;
  if t`Cat`Contra then 
    Cat := CotensorCategory( Prune(Arrows(t`Cat)) cat [1], { {x+1 : x in S} : S in t`Cat`Repeats } );
  else
    Cat := TensorCategory( Arrows(t`Cat) cat [1], { {x+1 : x in S} : S in t`Cat`Repeats } join {{0}} );
  end if;
  s := Tensor( D, C, F, Cat );
  if assigned t`CoordImages then
    s`CoordImages := Eltseq(t);
  end if;
  if assigned t`Coerce then
    s`Coerce := t`Coerce cat [* hom< C -> C | <C.1,C.1> > *];
  end if;

  if __SANITY_CHECK then
    printf "Sanity check turned on... (AssociatedForm)";
    I := CartesianProduct( < Basis(X) : X in __FRAME(t) > );
    assert forall{ x : x in I | Coordinates(t`Codomain,< x[i] : i in [1..#x-1]> @ t)[Index(Basis(t`Codomain),x[#x])] eq (x@s)[1] };
    printf "  DONE!\n";
  end if;
  return s;
end intrinsic;

intrinsic IsAntisymmetric( t::TenSpcElt ) -> BoolElt
{Decides if t is antisymmetric.}
  if assigned t`Reflexive`Antisymmetric then
    return t`Reflexive`Antisymmetric;
  end if;
  if exists{ D : D in t`Domain | Dimension(D) ne Dimension(t`Domain[1]) } then
    t`Reflexive`Alternating := false;
    return false;
  end if;
  try
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;
  if t`Valence eq 3 then
    F := SystemOfForms(t);
    isit := forall{ f : f in F | Transpose(f) eq -f };
  else
    G := Parent(t`Permutation);
    Stab := Stabilizer(G,GSet(G),GSet(G)!0);

    ShuffleWithSign := function(t,g)
      s := Eltseq(Shuffle(t,g));
      if Sign(g) eq -1 then
        s := [ -x : x in s ];
      end if;
      return s;
    end function;

    isit := forall{ g : g in Stab | Eltseq(t) eq ShuffleWithSign(t,g) };
  end if;
  t`Reflexive`Antisymmetric := isit;
  if Characteristic(BaseRing(t)) ne 2 then
    t`Reflexive`Alternating := isit;
  end if;
  return isit;
end intrinsic;

intrinsic IsAlternating( t::TenSpcElt ) -> BoolElt
{Decides if t is alternating.}
  K := BaseRing(t);
  if Characteristic(K) ne 2 then
    return IsAntisymmetric(t);
  end if;
  if not IsAntisymmetric(t) then
    return false;
  end if;
  isit := forall{ i : i in [1..Dimension(t`Domain[1])] | 
          Slice(t, [ {i} : j in [1..#t`Domain] ] cat [{1..Dimension(t`Codomain)}] ) eq [0 : j in [1..Dimension(t`Codomain)]] };
  t`Reflexive`Alternating := isit;
  return isit;
end intrinsic;

intrinsic IsSymmetric( t::TenSpcElt ) -> BoolElt
{Decides if t is symmetric.}
  if assigned t`Reflexive`Symmetric then
    return t`Reflexive`Symmetric;
  end if;
  if exists{ D : D in t`Domain | Dimension(D) ne Dimension(t`Domain[1]) } then
    t`Reflexive`Symmetric := false;
    return false;
  end if;
  try
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;
  if t`Valence eq 3 then
    F := SystemOfForms(t);
    isit := forall{ f : f in F | Transpose(f) eq f };
  else
    G := Parent(t`Permutation);
    Stab := Stabilizer(G,GSet(G),GSet(G)!0);
    isit := forall{ g : g in Stab | Eltseq(t) eq Eltseq(Shuffle(t,g)) };
  end if;
  t`Reflexive`Symmetric := isit;
  return isit;
end intrinsic;

// ==============================================================================
//                               Categorical stuff
// ==============================================================================
// Only implemented for homotopism category.
// ------------------------------------------------------------------------------
//                                     Submaps
// ------------------------------------------------------------------------------
intrinsic Subtensor( t::TenSpcElt, D::List, C::. ) -> TenSpcElt
{Returns the smallest submap of t containing the Cartesian product of D in the domain and C in the codomain.}
  require #D eq #t`Domain : "Argument 2 does not match the valence of argument 1.";
  if exists{ X : X in Frame(t) | Type(X) notin __LIST } then
    passed, t, _, err := __TensorOnVectorSpaces(t);
    require passed : err;
  end if;
  // Get the domain and codomain down to standard objects. 
  // Also, check that they lie in the correct spaces.  
  Dom := __GenerateDomain( t, D );
  require Type(Dom) ne BoolElt : "Argument 2 is not in the domain.";
  Cod := __GenerateCodomain( t, C );
  require Type(Cod) ne BoolElt : "Argument 3 is not in the codomain.";

  // Fill the image
  gens := CartesianProduct( < Basis(Dom[i]) : i in [1..#t`Domain] > );
  Cod := sub< t`Codomain | Cod, { g @ t : g in gens } >;
  if __HasBasis(C) then // remove superfluous generators
    Cod := sub< t`Codomain | Basis(Cod) >;
  end if;

  F := function(x)
    return < (t`Domain)[i]!(x[i]) : i in [1..#t`Domain] > @ t;
  end function;

  s := __GetTensor( Dom, Cod, F : Cat := t`Cat );
  return s;
end intrinsic;

intrinsic Subtensor( t::TenSpcElt, S::List ) -> TenSpcElt
{Returns the smallest submap of t containing S. 
The first v entries of S are contained in the domain of t, and the last entry of S is contained in the codomain of t.}
  return Subtensor( t, S[1..t`Valence-1], S[t`Valence] );
end intrinsic;

intrinsic IsSubtensor( t::TenSpcElt, s::TenSpcElt ) -> BoolElt
{Decides if s is a subtensor of t.}
  require t`Cat eq s`Cat : "Tensors not in the same category.";
  if exists{ X : X in Frame(t) | Type(X) notin __LIST } then
    passed, t, H2, err := __TensorOnVectorSpaces(t);
    require passed : err;
  end if;
  if exists{ X : X in Frame(s) | Type(X) notin __LIST } then
    passed, s, _, err := __TensorOnVectorSpaces(s);
    require passed : err;
  end if;
  if Parent(t) ne Parent(s) then
    return false;
  end if;

  d := forall{ i : i in [1..#s`Domain] | forall{ b : b in Basis(s`Domain[i]) | IsCoercible(t`Domain[i],b) } };
  if d then
    c := forall{ b : b in Basis(s`Codomain) | IsCoercible(t`Codomain,b) };
  else
    return false;
  end if;
  return c;
end intrinsic;

// ------------------------------------------------------------------------------
//                                     Ideals
// ------------------------------------------------------------------------------
intrinsic LocalIdeal( M::TenSpcElt, D::List, C::., I::{RngIntElt} ) -> TenSpcElt
{Returns the smallest submap of M which is a local ideal containing D in the domain and C in the codomain. 
Here, I is a subset of integers corresponding to the Cartesian factors in the domain.}
  require Arrows(M`Cat) eq [ 1 : i in [1..M`Valence] ] : "Ideal not implemented for this category.";
  require #D eq #M`Domain : "Argument 2 does not match the valence of argument 1.";
  require forall{ X : X in Frame(M) | Type(X) in __LIST } : "Domain and codomain must be vector spaces.";
  require I subset {1..#M`Domain} : "Argument 4 contains unknown values.";
  I := {@ M`Valence-s : s in I @};
  // Get the domain and codomain down to standard objects. 
  // Also, check that they lie in the correct spaces.  
  Dom := __GenerateDomain( M, D );
  require Type(D) ne BoolElt : "Argument 2 is not in the domain.";
  Cod := __GenerateCodomain( M, C );
  require Type(C) ne BoolElt : "Argument 3 is not in the codomain.";

  // Fill the image.
  Im := {};
  for s in I do
    temp := [* X : X in Dom *];
    temp[s] := M`Domain[s];
    gens := CartesianProduct( < Basis( temp[i] ) : i in [1..#M`Domain] > );
    Im join:= { g : g in gens };
  end for;
  Cod := sub< M`Codomain | Cod, { g @ M : g in Im } >;
  Cod := sub< M`Codomain | Basis(Cod) >; // reduce the number of generators.
  
  F := function(x)
    return < (M`Domain)[i]!(x[i]) : i in [1..#M`Domain] > @ M;
  end function;

  N := __GetTensor( Dom, Cod, F : Cat := M`Cat );
  return N;
end intrinsic;

intrinsic LocalIdeal( M::TenSpcElt, S::List, I::{RngIntElt} ) -> TenSpcElt
{Returns the smallest submap of M which is a local ideal containing S. 
Here, I is a subset of integers corresponding to the Cartesian factors in the domain.}
  return LocalIdeal( M, S[1..M`Valence-1], S[M`Valence], I );
end intrinsic;

intrinsic LocalIdeal( M::TenSpcElt, N::TenSpcElt, I::{RngIntElt} ) -> TenSpcElt
{Returns the smallest submap of M which is a local ideal containing N. 
Here, I is a subset of integers corresponding to the Cartesian factors in the domain.}
  return LocalIdeal( M, [* x : x in N`Domain *], N`Codomain, I );
end intrinsic;

intrinsic IsLocalIdeal( M::TenSpcElt, N::TenSpcElt, S::{RngIntElt} ) -> BoolElt
{Decide if N is a local ideal of M. 
Here, S is a subset of integers corresponding to the Cartesian factors in the domain.}
  require M`Cat eq N`Cat : "Tensors not in the same category.";
  require Arrows(M`Cat) eq [ 1 : i in [1..M`Valence] ] : "Ideals not implemented for this category.";
  require forall{ X : X in Frame(M) | Type(X) in __LIST } : "Domain and codomain of tensors must be vector spaces.";
  require forall{ X : X in Frame(N) | Type(X) in __LIST } : "Domain and codomain of tensors must be vector spaces.";
  if Parent(M) ne Parent(N) then
    return false;
  end if;
  n := #M`Domain;
  require S subset {1..n} : "Argument 3 contains unknown values.";
  S := {@ n-s+1 : s in S @};

  if not IsSubtensor(M,N) then
    return false;
  end if;

  // Check the definition.
  for s in S do
    temp := [* x : x in N`Domain *];
    temp[s] := M`Domain[s];
    gens := CartesianProduct( < Basis( temp[i] ) : i in [1..n] > );
    if exists{ g : g in gens | g @ M notin N`Codomain } then
      return false;
    end if;
  end for;
  return true;
end intrinsic;

intrinsic Ideal( M::TenSpcElt, D::List, C::. ) -> TenSpcElt
{Returns the smallest submap of M containing D in the domain and C in the codomain that is an ideal of M.}
  return LocalIdeal( M, D, C, {1..#M`Domain} );
end intrinsic;

intrinsic Ideal( M::TenSpcElt, S::List ) -> TenSpcElt
{Returns the smallest submap of M containing S that is an ideal of M.}
  return LocalIdeal( M, S[1..M`Valence-1], S[M`Valence], {1..#M`Domain} );
end intrinsic;

intrinsic Ideal( M::TenSpcElt, N::TenSpcElt ) -> TenSpcElt
{Returns the smallest submap of M containing N that is an ideal of M.}
  require M`Valence eq N`Valence : "Valences do not match.";
  return LocalIdeal( M, [* x : x in N`Domain *], N`Codomain, {1..#M`Domain} );
end intrinsic;

intrinsic IsIdeal( M::TenSpcElt, N::TenSpcElt ) -> BoolElt
{Decides if N is an ideal of M.}
  return IsLocalIdeal( M, N, {1..#N`Domain} );
end intrinsic;

// ------------------------------------------------------------------------------
//                                    Quotients
// ------------------------------------------------------------------------------
intrinsic LocalQuotient( M::TenSpcElt, N::TenSpcElt, S::SetEnum : Check := true ) -> TenSpcElt, Hmtp
{Returns the local quotient of M by the local ideal N. 
Here, S is a subset of integers corresponding to the Cartesian factors in the domain.}
  require M`Cat eq N`Cat : "Tensors not in the same category.";
  require Arrows(M`Cat) eq [ 1 : i in [1..M`Valence] ] : "Quotient not implemented for this category.";
  if exists{ X : X in Frame(M) | Type(X) notin __LIST } then
    passed, M, H2, err := __TensorOnVectorSpaces(M);
    require passed : err;
  end if;
  if exists{ X : X in Frame(N) | Type(X) notin __LIST } then
    passed, N, _, err := __TensorOnVectorSpaces(N);
    require passed : err;
  end if;
  require Parent(M) eq Parent(N) : "Tensors are from different tensor spaces.";
  n := #M`Domain;
  require S subset {1..n} : "Argument 3 contains unknown values.";
  
  // Check S-ideal properties.
  if Check then
    require IsLocalIdeal( M, N, S ) : "Argument is not a local ideal.";
  end if;
  S := {@ n-s+1 : s in S @};

  D := [* *];
  projs := [* *];
  for i in [1..n] do
    if i in S then
      Q,pi := M`Domain[i] / N`Domain[i];
    else
      Q := M`Domain[i];
      pi := hom< Q -> Q | [ <x,x> : x in Basis( Q ) ] >;
    end if;
    Append( ~D, Q );
    Append( ~projs, pi );
  end for;
  C, pi := M`Codomain / N`Codomain;
  Append( ~projs, pi );

  F := function(x)
    return < x[i] @@ projs[i] : i in [1..n] > @ M @ pi;
  end function;

  Q := __GetTensor( D, C, F : Cat := M`Cat );
  H := __GetHomotopism( M, Q, projs : Cat := HomotopismCategory(M`Valence : Contravariant := M`Cat`Contra) );
  if assigned H2 then
    H := H2*H;
  end if;
  return Q, H;
end intrinsic;

intrinsic Quotient( M::TenSpcElt, N::TenSpcElt : Check := true ) -> TenSpcElt, Hmtp
{Returns the quotient of M by the ideal N.}
  require M`Cat eq N`Cat : "Tensors not in the same category.";
  require Arrows(M`Cat) eq [ 1 : i in [1..M`Valence] ] : "Quotient not implemented for this category.";
  if Check then
    require IsIdeal( M, N ) : "Arugment is not an ideal.";
  end if;
  return LocalQuotient( M, N, {1..#M`Domain} : Check := false );
end intrinsic;

intrinsic '/'( M::TenSpcElt, N::TenSpcElt ) -> TenSpcElt, Hmtp
{Returns the quotient M/N.}
  return Quotient(M,N);
end intrinsic;
