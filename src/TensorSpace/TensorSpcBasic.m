/*
  This file contains basic fucntions for tensor spaces (TenSpc).
*/


import "../GlobalVars.m" : __LIST, __SANITY_CHECK, __FRAME;
import "TensorSpc.m" : __GetTensorSpace;

__HasRandom := function( X )
  try 
    B := Random(X);
  catch e
    if assigned e`Object then
      return false;
    end if;
  end try;
  return true;
end function;

// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
intrinsic Valence( T::TenSpc ) -> RngIntElt
{Returns the valence of the tensor space T.}
  return T`Valence;
end intrinsic;

intrinsic Frame( T::TenSpc ) -> List
{Returns the modules in the frame of the tensor space T.}
  if T`Cat`Contra then
    return T`Frame[1..#T`Frame-1];
  end if;
  return T`Frame;
end intrinsic;

intrinsic BaseRing( T::TenSpc ) -> Rng
{Returns the base ring of the tensor space T.}
  return T`Ring;
end intrinsic;

intrinsic BaseField( T::TenSpc ) -> Fld
{Returns the base field of the tensor space T.}
  require IsField(T`Ring) : "Base ring is not a field.";
  return T`Ring;
end intrinsic;

intrinsic TensorCategory( T::TenSpc ) -> TenCat
{Returns the tensor category of the tensor space T.}
  return T`Cat;
end intrinsic;

intrinsic IsContravariant( T::TenSpc ) -> BoolElt
{Decides if T is a cotensor space.}
  return T`Cat`Contra;
end intrinsic;

intrinsic IsCovariant( T::TenSpc ) -> BoolElt
{Decides if T is a tensor space.}
  return not T`Cat`Contra;
end intrinsic;

intrinsic ChangeTensorCategory( T::TenSpc, C::TenCat ) -> TenSpc
{Returns the tensor space with the given category.}
  require T`Cat`Contra eq C`Contra : "Both must be co- or contravariant.";
  require T`Valence eq C`Valence : "Valence does not match.";
  return __GetTensorSpace( T`Ring, T`Mods, C );
end intrinsic;

intrinsic ChangeTensorCategory( ~T::TenSpc, C::TenCat )
{Returns the given tensor space with the given category.}
  require T`Cat`Contra eq C`Contra : "Both must be co- or contravariant.";
  require T`Valence eq C`Valence : "Valence does not match.";
  T`Cat := C;
end intrinsic;

intrinsic '.'( T::TenSpc, i::RngIntElt ) -> TenSpcElt
{T.i}
  require i ge 1 : "Integer must be positive.";
  M := T`Mod;
  d := Dimension(M);
  require i le d : "Integer should be in range [1.." cat IntegerToString(d) cat "].";
  gen := Eltseq(M.i @ T`UniMap);
  t := T!gen;
  t`Element := M.i;
  return t;
end intrinsic;

intrinsic Generators( T::TenSpc ) -> SeqEnum
{Returns the generators of T.}
  return [ T.i : i in [1..Dimension(T`Mod)] ];
end intrinsic;

intrinsic NumberOfGenerators( T::TenSpc ) -> RngIntElt
{Returns the number of generators of the tensor space T.}
  return Dimension(T`Mod);
end intrinsic;

intrinsic Ngens( T::TenSpc ) -> RngIntElt
{Returns the number of generators of the tensor space T.}
  return Dimension(T`Mod);
end intrinsic;

intrinsic Dimension( T::TenSpc ) -> RngIntElt
{Returns the dimension of T as a free R-module.}
  return Dimension(T`Mod);
end intrinsic;

intrinsic '#'( T::TenSpc ) -> RngIntElt
{Returns the cardinality of T.}
  R := T`Ring;
  require IsFinite(R) : "Base ring is not finite.";
  return #R^Ngens(T);
end intrinsic;

intrinsic Random( T::TenSpc ) -> TenSpcElt
{Returns a random element of T.}
  dims := [ Dimension(M) : M in T`Frame ];
  if exists{ d : d in dims | d eq 0 } then // to fix a bug when one entry is 0
    spaces := __FRAME(T);
    C := spaces[#spaces];
    F := function(x)
      return C!0;
    end function;
    t := Tensor( Frame(T), F, T`Cat );
    t`Parent := T;
    return t;
  end if;
  M := T`Mod;
  require __HasRandom(M) : "Base ring has no random algorithm.";
  m := Random(M);
  t := T!Eltseq(m @ T`UniMap);
  t`Element := m;
  return t;
end intrinsic;

intrinsic RandomTensor( R::Rng, S::[RngIntElt], Cat::TenCat ) -> TenSpcElt
{Returns a random tensor of the R-tensor space with the given dimensions and category.}
  require __HasRandom(R) : "Base ring has no random algorithm.";
  if Cat`Contra then
    require ISA(Type(R),Fld) : "Base ring must be a field for cotensors.";
    return Random(KCotensorSpace(R,S,Cat));
  end if;
  return Random(RTensorSpace(R,S,Cat));
end intrinsic;

intrinsic RandomTensor( R::Rng, S::[RngIntElt] ) -> TenSpcElt
{Returns a random tensor of the R-tensor space with the given dimensions.}
  require __HasRandom(R) : "Base ring has no random algorithm.";
  return Random(RTensorSpace(R,S));
end intrinsic;

intrinsic RandomCotensor( K::Fld, S::[RngIntElt] ) -> TenSpcElt
{Returns a random cotensor of the K-tensor space with the given dimensions.}
  require __HasRandom(K) : "Base ring has no random algorithm.";
  return Random(KCotensorSpace(K,S));
end intrinsic;

intrinsic UniversalTensorSpace( T::TenSpc ) -> TenSpc
{Returns the universal tensor space with the same base ring, frame, and category.}
  return __GetTensorSpace( T`Ring, T`Frame, T`Cat );
end intrinsic;

intrinsic UniversalCotensorSpace( T::TenSpc ) -> TenSpc
{Returns the universal cotensor space with the same base ring, frame, and category.}
  return __GetTensorSpace( T`Ring, T`Frame, T`Cat );
end intrinsic;

// Standard magma name
intrinsic Generic( T::TenSpc ) -> TenSpc
{Returns the universal tensor space with the same base ring, frame, and category.}
  return __GetTensorSpace( T`Ring, T`Frame, T`Cat );
end intrinsic;

intrinsic IsAlternating( T::TenSpc ) -> BoolElt
{Decides if the tensor space is alternating.}
  return forall{ t : t in Generators(T) | IsAlternating(t) };
end intrinsic;

intrinsic IsSymmetric( T::TenSpc ) -> BoolElt
{Decides if the tensor space is symmetric.}
  return forall{ t : t in Generators(T) | IsSymmetric(t) };
end intrinsic;

intrinsic IsAntisymmetric( T::TenSpc ) -> BoolElt
{Decides if the tensor space is antisymmetric.}
  return forall{ t : t in Generators(T) | IsAntisymmetric(t) };
end intrinsic;

// Must be a better way to do these.
intrinsic SymmetricSpace( T::TenSpc ) -> TenSpc
{Returns the largest subtensor space of T where every tensor is symmetric.}
  require forall{ X : X in T`Frame[1..T`Valence-1] | Dimension(X) eq Dimension(T`Frame[1]) } : "Incompatible frame.";
  return sub< T | [T!SymmetricTensor(t) : t in Generators(T)] >;
end intrinsic;

intrinsic AlternatingSpace( T::TenSpc ) -> TenSpc 
{Returns the largest subtensor space of T where every tensor is alternating.}
  require forall{ X : X in T`Frame[1..T`Valence-1] | Dimension(X) eq Dimension(T`Frame[1]) } : "Incompatible frame.";
  return sub<T | [T!AlternatingTensor(t) : t in Generators(T)]>;
end intrinsic;

intrinsic AntisymmetricSpace( T::TenSpc ) -> TenSpc 
{Returns the largest subtensor space of T where every tensor is antisymmetric.}
  require forall{ X : X in T`Frame[1..T`Valence-1] | Dimension(X) eq Dimension(T`Frame[1]) } : "Incompatible frame.";
  return sub< T | [T!AntisymmetricTensor(t) : t in Generators(T)] >;
end intrinsic;

intrinsic AsCotensorSpace( t::TenSpcElt ) -> TenSpc, Mtrx
{Returns the associated cotensor space of the tensor t.}
  require ISA(Type(BaseRing(t)),Fld) : "Base ring must be a field.";
  if t`Cat`Contra then
    U := Generic(Parent(t));
    return sub< U | [t] >;
  end if;
  F := Foliation(t,0);
  part := t`Cat`Repeats;
  for S in part do
    if 0 in S then
      temp := S;
      Exclude(~part,S);
      if #temp gt 1 then
        Exclude(~temp,0);
        Include(~part,temp);
      end if;
    end if;
  end for;
  Cat := CotensorCategory(Prune(Arrows(t`Cat)),part); 
  CT := CotensorSpace(t`Domain, Cat);
  S := sub< CT`Mod | [ CT`Mod!F[i] : i in [1..Nrows(F)] ] >;
  CT`Mod := S;
  return CT, F;
end intrinsic;

intrinsic AsTensorSpace( t::TenSpcElt, i::RngIntElt ) -> TenSpc, Mtrx
{Returns the associated tensor space of the tensor in the i coordinate.}
  require i gt 0 : "Index must be positive.";
  F := Foliation(t,i);
  surj := [0] cat Reverse(Remove([1..#t`Domain],t`Valence-i));
  part := { { Index(surj,x)-1 : x in S | x in surj } : S in t`Cat`Repeats };
  if {} in part then Exclude(~part,{}); end if;
  spaces := Frame(t);
  Remove(~spaces,t`Valence-i);
  if t`Cat`Contra then
    Cat := TensorCategory(Remove(Arrows(t`Cat),i) cat [1],part join {{0}}); 
  else
    Cat := TensorCategory(Remove(Arrows(t`Cat),i),part); 
  end if;
  T := TensorSpace(spaces,Cat);
  S := sub< T`Mod | [ T`Mod!F[i] : i in [1..Nrows(F)] ] >;
  T`Mod := S;
  return T, F;
end intrinsic;

intrinsic AsTensor( T::TenSpc ) -> TenSpcElt
{Returns the associated tensor.}
  require Dimension(T`Mod) ge 1 : "0-dimensional space.";
  s := [];
  for i in [1..Dimension(T)] do
    s cat:= Eltseq(T`Mod.i @ T`UniMap);
  end for;
  if T`Cat`Contra then
    Cat := TensorCategory( Arrows(T`Cat), T`Cat`Repeats ); 
    d := Degree(Generic(T)`Mod);
    indices := [ i+(j-1)*d : j in [1..Ngens(T`Mod)], i in [1..d] ];
    t := Tensor(BaseRing(T), [ Dimension(X) : X in T`Frame[1..#T`Frame-1] ] cat [Dimension(T)], s[indices], Cat);
  else
    Cat := TensorCategory( [1] cat Arrows(T`Cat), T`Cat`Repeats join {{T`Valence}} );
    t := Tensor(BaseRing(T),[Dimension(T)] cat [ Dimension(X) : X in T`Frame ], s);
  end if;
  return t;
end intrinsic; 

// ==============================================================================
//                                   Categorical
// ==============================================================================
intrinsic SubConstructor( T::TenSpc, L::Any ) -> TenSpc, Map
{Returns the subtensor space of T, generated by the entries in L.}
  /* get everything down to a list of elements to coerce */
  L := Flat(L);
  subspaces := [* t : t in L | Type(t) eq TenSpc *];
  others := [* t : t in L | Type(t) ne TenSpc *];
  gens := [* Generators(S) : S in subspaces *];
  nL := others;
  for x in gens do
    nL cat:= [* y : y in x *];
  end for;

  try
    require forall{ t : t in nL | IsCoercible(T,t) } : "Elements are not contained in tensor space.";
  catch err
    error "Entries cannot be coerced into tensor space.";
  end try;

  nL := [* T!t : t in nL *];
  try
    for t in nL do
      _ := Eltseq(t);
    end for;
  catch err
    error "Cannot compute structure constants of tensors.";
  end try;

  dims := [ Dimension(X) : X in T`Frame ];
  M := sub< T`Mod | [ Eltseq(t) @@ T`UniMap : t in nL ] >;
  S := __GetTensorSpace( T`Ring, T`Frame, T`Cat );
  S`Mod := M;
  S`UniMap := T`UniMap;
  return S;
end intrinsic;

//intrinsic SubtensorSpace( T::TenSpc, L::[TenSpcElt] ) -> TenSpc, Map
//{Returns the subtensor space generated by the sequence of tensors.}
//  require forall{ t : t in L | IsCoercible(T,t) } : "Tensors are not contained in tensor space.";
//  try
//    for t in L do
//      _ := Eltseq(t);
//    end for;
//  catch err
//    require false : "Cannot compute structure constants of tensors.";
//  end try;
//  dims := [ Dimension(X) : X in T`Frame ];
//  gens := [];
//  for t in L do
//    if assigned t`Element and IsCoercible(T`Mod, t`Element) then
//      Append(~gens, T`Mod!t`Element);
//    else
//      Append(~gens, Eltseq(t) @@ T`UniMap);
//    end if;
//  end for;
//  M := sub< T`Mod | gens >;
//  S := __GetTensorSpace( T`Ring, T`Frame, T`Cat );
//  S`Mod := M;
//  S`UniMap := T`UniMap;
//  return S;
//  "SubtensorSpace is being depreciated. Use sub< ... > instead.";
//  return sub<T|L>;
//end intrinsic;

//intrinsic SubtensorSpace( T::TenSpc, t::TenSpcElt ) -> TenSpc, Map
//{Returns the subtensor space generated by t.}
//  "SubtensorSpace is being depreciated. Use sub< ... > instead.";
//  return sub<T|t>;
//end intrinsic;

intrinsic IsSubtensorSpace( T::TenSpc, S::TenSpc ) -> BoolElt
{Decides if S is a subtensor space of T.}
  return S subset T;
end intrinsic;

//intrinsic Quotient( T::TenSpc, S::TenSpc ) -> TenSpc, Map
//{Returns the quotient tensor space of T by S.}
//  require S subset T : "Tensor space is not a subtensor space.";
//  Q,pi := T`Mod/S`Mod;
//  U := __GetTensorSpace( T`Ring, T`Frame, T`Cat );
//  U`Mod := Q;
//  U`UniMap := pi^-1 * T`UniMap;
//  return U;
//  "Quotient is being depreciated. Use `/' or quo< ... > instead.";
//  return quo<T|S>;
//end intrinsic;

intrinsic QuoConstructor( T::TenSpc, X::Any ) -> TenSpc, Map
{Returns the quotient tensor space of T by X.}
  try
    S := SubConstructor(T,X);
  catch err
    error "Entries do not generate a subtensor space.";
  end try;
  Q,pi := T`Mod/S`Mod;
  U := __GetTensorSpace( T`Ring, T`Frame, T`Cat );
  U`Mod := Q;
  U`UniMap := pi^-1 * T`UniMap;
  return U;
end intrinsic;

intrinsic '/'( T::TenSpc, S::TenSpc ) -> TenSpc, Map
{Returns the quotient tensor space T/S.}
  return quo<T|S>;
end intrinsic;
