/* 
    Copyright 2016, 2017, Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


/*
  Thsi file contains basic intrinsics for homotopisms (Hmtp).
*/


import "Hom.m" : __GetHomotopism;

// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
intrinsic Valence( H::Hmtp ) -> RngIntElt
{Returns the valence of the underlying category of the homotopism H.}
  return Valence(TensorCategory(H));
end intrinsic;

intrinsic Domain( H::Hmtp ) -> TenSpcElt
{Returns the domain of H.}
  return H`Domain; // Come back to this. H`Domain isn't aways defined.
end intrinsic;

intrinsic Codomain( H::Hmtp ) -> TenSpcElt
{Returns the codomain of H.}
  return H`Codomain; // Come back to this. H`Codomain isn't aways defined.
end intrinsic;

intrinsic Maps( H::Hmtp ) -> List
{Returns the list of maps for H.}
  return H`Maps;
end intrinsic;

// There is a more general function for this.... requires more thought.
intrinsic Kernel( H::Hmtp ) -> TenSpcElt, List
{Returns the kernel as a subtensor of the domain of H.}
  dom := Frame(H`Domain);
  cod := Frame(H`Codomain);
  maps := H`Maps;
  v := H`Cat`Valence-1;
  K_frame := ChangeUniverse([],Parent(H`Domain`Domain[1])); //workaround
  for i in Reverse([0..v]) do
    if i @ H`Cat`Arrows eq 1 then
      try 
        S := Kernel(maps[v-i+1]);
      catch err
        error "Cannot compute the kernel in position",i;
      end try;
    elif i @ H`Cat`Arrows eq -1 then
      try 
        S := Image(maps[v-i+1]);
      catch err
        error "Cannot compute the image in position",i;
      end try;
    else
      S := dom[v-i+1];
    end if;
    Append(~K_frame, S);
  end for;
  F := func< x | x @ H`Domain >;
  return Tensor(K_frame,F,H`Domain`Cat);
end intrinsic;

// There is a more general function for this.... requires more thought.
intrinsic Image( H::Hmtp ) -> TenSpcElt, List
{Returns the image of H as a subtensor of the codomain of H.}
  dom := Frame(H`Domain);
  cod := Frame(H`Codomain);
  maps := H`Maps;
  v := H`Cat`Valence-1;
  I_frame := ChangeUniverse([],Parent(H`Domain`Domain[1]));
  for i in Reverse([0..v]) do
    if i @ H`Cat`Arrows eq 1 then
      try 
        S := Image(maps[v-i+1]);
      catch err
        error "Cannot compute the image in position",i;
      end try;
    elif i @ H`Cat`Arrows eq -1 then
      try 
        S := Kernel(maps[v-i+1]);
      catch err
        error "Cannot compute the kernel in position",i;
      end try;
    else
      S := dom[v-i+1];
    end if;
    Append(~I_frame, S);
  end for;
  F := func< x | x @ H`Codomain >;
  return Tensor(I_frame,F,H`Codomain`Cat);
end intrinsic;

intrinsic TensorCategory( H::Hmtp ) -> TenCat
{Returns the tensor category of H.}
  return H`Cat;
end intrinsic;

intrinsic ChangeTensorCategory( H::Hmtp, C::TenCat ) -> Hmtp
{Returns the homotopism with the given category.}
  return __GetHomotopism(H`Domain, H`Codomain, H`Maps : Cat := C );
end intrinsic;

intrinsic ChangeTensorCategory( ~H::Hmtp, C::TenCat )
{Returns the homotopism with the given category.}
  H`Cat := C;
end intrinsic;

intrinsic '.'( H::Hmtp, i::RngIntElt ) -> Map
{Returns the map on the ith coordinate.}
  M := Maps(H);
  require i in [0..#M-1] : "Integer should be in range [0.." cat IntegerToString(#M-1) cat "].";
  return M[#M-i];
end intrinsic;


intrinsic Shuffle( H::Hmtp, g::GrpPermElt ) -> Hmtp
{Returns the shuffle of H, in a tensor category of valence v, by the permutation g on the set [0..v-1].}
  v := Valence(H);
  Cat_old := TensorCategory(H);

  // check things based on co-/ contra- variance.
  if Cat_old`Contra then
    require Labelling(Parent(g)) in {{1..v-1},{0..v-1}} : "Permutation must act on {1..v-1}.";
    if Labelling(Parent(g)) eq {1..v-1} then
      g := Sym({0..v-1})!([0] cat Eltseq(g));
    else
      require 0^g eq 0 : "Permutation must fix 0 for cotensors.";
    end if;
  else
    require Labelling(Parent(g)) eq {0..v-1} : "Permuation must act on {0..v-1}.";
  end if;

  // stop if g is trivial
  if Parent(g)!1 eq g then
    return H;
  end if;

  // build the new category
  Cat_new := New(TenCat);
  Cat_new`Valence := v;
  Cat_new`Arrows := map< {0..v-1} -> {-1,0,1} | x :-> (x^g) @ Cat_old`Arrows >;
  Cat_new`Repeats := {{x^(g^-1) : x in S} : S in Cat_old`Repeats};
  Cat_new`Contra := Cat_old`Contra;

  // rearrange the maps
  g_elt := Reverse([v-i : i in Eltseq(g)]);
  M := Maps(H)[g_elt];

  // shuffle the domain and codomain
  try
    dom := Shuffle(Domain(H), g);
    cod := Shuffle(Codomain(H), g);
    H_shuf := Homotopism(dom, cod, M, Cat_new);
  catch err
    H_shuf := Homotopism(M, Cat_new);
  end try;
  
  return H_shuf;
end intrinsic;

intrinsic Shuffle( H::Hmtp, g::SeqEnum[RngIntElt] ) -> Hmtp
{Returns the shuffle of H, in a tensor category of valence v, by the permutation given by g on the set [0..v-1].}
    if TensorCategory(H)`Contra then
    isit, perm := IsCoercible(Sym({1..Valence(H)-1}), g);
    if not isit then
      isit, perm := IsCoercible(Sym({0..Valence(H)-1}), g);
      require isit : "Permutation must act on {1..v}.";
      require Index(g, 0) eq 1 : "Permutation must fix 0.";
    end if;
  else
    isit, perm := IsCoercible(Sym({0..Valence(H)-1}), g);
    require isit : "Permutation must act on {0..v}.";
  end if;
  return Shuffle(H, perm);
end intrinsic;
