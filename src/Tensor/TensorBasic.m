/* 
    Copyright 2016--2025 Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


/*
  This file contains basic functions for tensors (TenSpcElt).
*/


import "../GlobalVars.m" : __SANITY_CHECK, __FRAME;
import "Tensor.m" : __GetTensor, __TensorOnVectorSpaces;
import "../Homotopism/Hom.m" : __GetHomotopism;
import "../TensorCategory/TensorCat.m" : __TensorCatSanity;

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
  S := sub< S | Basis(S) >; // Magma work-around : remove superfluous generators
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

  // Initial solve
  R := BaseRing(t);
  D := t`Domain;
  Rad := Radical(t);

  // Construct projections
  dom := [**];
  proj := [**];
  for i in [1..#D] do
    Q,pi := D[i]/Rad[i];
    Q_basis := [b @@ pi : b in Basis(Q)];
    Append(~dom, Q);
    Append(~proj, pi);
  end for;
  // Include the codomain stuff
  Append(~proj, hom< t`Codomain -> t`Codomain | [ <b,b> : b in Basis(t`Codomain) ] >);

  F := function(x)
    return < x[i] @@ proj[i] : i in [1..#x] > @ t;
  end function;

  s := __GetTensor( dom, t`Codomain, F : Cat := t`Cat );
  s`Radicals := [* sub< dom[i] | > : i in [1..#dom] *];
  if assigned t`Coerce then
    s`Coerce := [* t`Coerce[i] * proj[i] : i in [1..#proj] *];
  end if;
  H := Homotopism( t, s, proj, HomotopismCategory(Valence(t)) : Check := false);
  if assigned H2 then
    H := H2*H;
  end if;

  t`Nondegenerate := < s, H >;
  return s, H;
end intrinsic;

intrinsic IsNondegenerate( t::TenSpcElt ) -> BoolElt
{Decides if t is nondegenerate.}
  return forall{a : a in [1..Valence(t)-1] | Dimension(Radical(t, a)) eq 0};
end intrinsic;

intrinsic IsDegenerate( t::TenSpcElt ) -> BoolElt
{Decides if t is nondegenerate.}
  return not IsNondegenerate(t); 
end intrinsic;

intrinsic FullyNondegenerateTensor( t::TenSpcElt ) -> TenSpcElt, Hmtp
{Returns the fully nondegenerate tensor of t and a homotopism.}
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
  H := Homotopism(t, full_s, H`Maps[1..#H`Maps-1] cat [* H`Maps[#H`Maps] * inc *], CohomotopismCategory(Valence(t)) : Check := false);
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
  if assigned t`Coerce then
    Coerce := t`Coerce cat [* hom< C -> C | <C.1,C.1> > *];
  else
    Coerce := false;
  end if;
  s := __GetTensor( D, C, F : Cat := Cat, Co := Coerce );
  if assigned t`CoordImages then
    s`CoordImages := Eltseq(t);
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
