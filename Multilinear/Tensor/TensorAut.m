/*
  This file contains intrinsics for computing autotopism groups for tensors.
*/


import "../GlobalVars.m" : __LIST, __SANITY_CHECK, __GLUE;

__THRESHOLD := 100000;

__UserWarning := function( S, ord, q, dims, out )
  count := 0;
  X := Random(GL(Nrows(S[1]),q));
  Y := Random(GL(Ncols(S[1]),q));
  Z := Random(GL(#S,q));
  tt := Cputime();
  if not out then
    repeat
      S_conj := [ X * s * Transpose(Y) : s in S ];
      count +:= 1;
    until Cputime(tt) gt 0.1;
  else
    repeat
      S_conj := [ X * s * Transpose(Y) : s in S ];
      S_out := [ &+[ Z[i][j]*S[i] : i in [1..#S] ] : j in [1..#S] ];
      count +:= 1;
    until Cputime(tt) gt 0.1;
  end if;
  timing := Cputime(tt);
  "WARNING!";
  pos_dims := [dims[j] : j in [1..3] | dims[j] ne 0];
  s := Sprintf( "  Brute-force search through GL(%o, %o)", pos_dims[1], q );
  for i in [2..#pos_dims] do
    s cat:= Sprintf( " x GL(%o, %o)", pos_dims[i], q );
  end for;
  if ord lt 10^9 then
    o := Sprintf( "  Order: %o\n", ord );
  else
    digits := Floor(Log(10,ord));
    o := Sprintf( "  Order: %oe+%o\n", Round(ord / 10^digits), digits );
  end if;
  ETA := ord/count * timing;
  if ETA gt 60 then
    ETA /:= 60;
    if ETA gt 60 then
      ETA /:= 60;
      t_measure := "hr";
    else
      t_measure := "min";
    end if;
  else
    t_measure := "sec";
  end if;
  if ETA lt 10^9 then
    t := Sprintf( "  Time: ~%o " cat t_measure, Round(ETA) );
  else
    digits := Floor(Log(10,ETA));
    t := Sprintf( "  Time: ~%oe+%o " cat t_measure, Round(ETA / 10^digits), digits );
  end if;
  return s cat "\n" cat o cat t;
end function;

// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                   Intrinsics
// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
// ==============================================================================
//                                    Tensors
// ==============================================================================
intrinsic IsometryGroup( T::TenSpcElt : DisplayStructure := true, Warning := true ) -> GrpMat
{Returns the isometry group of the 2-tensor T.}
  require T`Valence eq 2 : "Tensor must have valence 2.";
  if assigned T`Bimap`Isom then
    return T`Bimap`Isom;
  end if;
  try
    require Dimension(T`Domain[1]) eq Dimension(T`Domain[2]) : "Factors in domain must be isomorphic.";
  catch err
    error "Cannot extract vector space structure.";
  end try;
  try
    _ := Eltseq(T);
  catch err
    error "Cannot compute structure constants.";
  end try;

  S := SystemOfForms(T);
  try 
    // see if StarAlg will accept it
    I := IsometryGroup(S : DisplayStructure := DisplayStructure);
  catch err
    // resort to brute-force if finite field
    d := Dimension(T`Domain[1]);
    K := BaseRing(T);
    require ISA(Type(K), FldFin) : "Field must be finite.";
    ord := #GL(d,K);
    
    // brute-force warning
    if Warning and (ord ge __THRESHOLD) then
      __UserWarning( S, ord, #K, [d,0,0], false );
    end if;

    gens := [];
    for X in GL(d,K) do
      M := Matrix(X);
      S_conj := [ M * s * Transpose(M) : s in S ];
      if S eq S_conj then
        Append(~gens, X);
      end if;
    end for;
    I := sub< GL(d,K) | gens >;
  end try;

  I`DerivedFrom := < T, [2] >;
  T`Bimap`Isom := I;
  return I;
end intrinsic;

intrinsic PseudoIsometryGroup( T::TenSpcElt : Warning := true ) -> GrpMat
{Returns the pseudo-isometry group of the 2-tensor T.}
  require T`Valence eq 2 : "Tensor must have valence 2.";
  if assigned T`Bimap`PIsom then
    return T`Bimap`PIsom;
  end if;
  try
    require Dimension(T`Domain[1]) eq Dimension(T`Domain[2]) : "Factors in domain must be isomorphic.";
  catch err
    error "Cannot extract vector space structure.";
  end try;
  try
    _ := Eltseq(T);
  catch err
    error "Cannot compute structure constants.";
  end try;

  S := SystemOfForms(T);
  try 
    // see if small genus will accept it
    PI := PseudoIsometryGroupSG(T);
  catch err
    // resort to brute-force
    d := Dimension(T`Domain[1]);
    e := Dimension(T`Codomain);
    K := BaseRing(T);
    require ISA(Type(K), FldFin) : "Field must be finite.";
    ord_V := #GL(d,K);
    ord_W := #GL(e,K);
    ord := ord_V * ord_W;
    
    // brute-force warning
    if Warning and (ord ge __THRESHOLD) then
      __UserWarning( S, ord, #K, [d,0,e], true );
    end if;

    gens := [];
    for X in GL(d,K) do
      M := Matrix(X);
      S_conj := [ M * s * Transpose(M) : s in S ];
      for Y in GL(e,K) do
        N := Matrix(Y);
        S_out := [ &+[ N[i][j]*S[i] : i in [1..e] ] : j in [1..e] ];
        if S_out eq S_conj then
          Append(~gens, DiagonalJoin(M,N));
        end if;
      end for;
    end for;
    PI := sub< GL(d+e,K) | gens >;
  end try;

  PI`DerivedFrom := < T, [2,0] >;
  T`Bimap`PIsom := PI;
  return PI;
end intrinsic;

intrinsic AutotopismGroup( T::TenSpcElt : Warning := true ) -> GrpMat
{Returns the autotopism group of the 2-tensor T.}
  require T`Valence eq 2 : "Tensor must have valence 2.";
  if assigned T`Bimap`Aut then
    return T`Bimap`Aut;
  end if;
  try
    _ := Eltseq(T);
  catch err
    require Type(T) ne TenSpcElt : "Cannot compute structure constants.";
  end try;
  
  // trivial case
  if forall{ x : x in Arrows(T`Cat) | x eq 0 } then
    dims := [];
    ind := [];
    for P in T`Cat`Repeats do
      i := Random(P);
      Append(~ind, i);
      Append(~dims, Dimension(__GLUE(T)[2-i+1]));
    end for;
    A := sub< GL(&+ind, BaseRing(T)) | >;
    A`DerivedFrom := < T, ind >;
    T`Bimap`Aut := A;
    return A;
  end if;

  // special cases: 2 modules linked
  if exists(P){ P : P in T`Cat`Repeats | #P eq 2 } then
    perm := [ Random({0,1,2} diff P), Minimum(P), Maximum(P) ];
    sigma := Sym({0,1,2})!perm;
    // shuffle to the {{0},{1,2}} case
    S := Shuffle(T, sigma);
    if 0 @ S`Cat`Arrows eq 0 then
      A := IsometryGroup(S : Warning:=Warning);
      A`DerivedFrom := < T, [2^(sigma^-1)] >;
    else
      if 1 @ S`Cat`Arrows ne 0 then
        A := PseudoIsometryGroup(S : Warning:=Warning);
      else
        C, pi := Coradical(S);
        if Dimension(C) eq 0 then
          A := sub< GL(Dimension(S`Codomain), BaseRing(T)) | >;
        else
          bas := [ b @@ pi : b in Basis(C) ];
          bas_comp := Basis(Complement(S`Codomain,sub<S`Codomain|bas>));
          T := Matrix( bas cat bas_comp );
          gens := [ T^-1 * DiagonalJoin( x, IdentityMatrix(Dimension(S`Codomain)-Dimension(C),BaseRing(T)) ) * T : 
            x in Generators( GL(Dimension(C), BaseRing(T)) ) ];
          A := sub< Parent(gens[1]) | gens >;
        end if;
        A`DerivedFrom := < T, [0^(sigma^-1)] >;
      end if;
      if 1 @ S`Cat`Arrows ne 0 @ S`Cat`Arrows then
        _, pi2 := Induce(A, 2);
        _, pi0 := Induce(A, 0);
        A := sub< Generic(A) | [ DiagonalJoin( (X@pi2)^-1, X@pi0 ) : X in Generators(A) ] >;
        A`DerivedFrom := < T, [2^(sigma^-1),0^(sigma^-1)] >;
      end if;
    end if;
    T`Bimap`Aut := A;
    return A;
  end if;

  S := SystemOfForms(T);
  K := BaseRing(T);
  require ISA(Type(K), FldFin) : "Field must be finite.";
  if T`Cat`Repeats eq {{0,1,2}} then
    // all three linked
    d := Dimension(T`Domain[1]);
    ord := #GL(d,K);

    // brute-force warning
    if Warning and (ord ge __THRESHOLD) then
      __UserWarning( S, ord, #K, [d,0,0], true );
    end if; 

    gens := [];
    for X in GL(d,K) do
      M := Matrix(X);
      S_conj := [ M * s * Transpose(M) : s in S ];
      S_out := [ &+[ M[i][j]*S[i] : i in [1..d] ] : j in [1..d] ];
      if S_out eq S_conj then
        Append(~gens, X);
      end if;
    end for;
    A := sub< GL(d,K) | gens >;
    A`DerivedFrom := < T, [2] >;
  else
    // nothing is linked
    Dims := Reverse([ Dimension(X) : X in __GLUE(T) ]);
    OverGrp := [* *];
    PrintOut := [];
    for i in [2,1,0] do
      if i @ T`Cat`Arrows ne 0 then
        Append(~OverGrp, GL(Dims[i+1], K));
        Append(~PrintOut, Dims[i+1]);
      else
        Append(~OverGrp, sub< GL(Dims[i+1], K) | >);
        Append(~PrintOut, 0);
      end if;
    end for;
    ord := &*[ #G : G in OverGrp ];
  
    // brute-force warning
    if Warning and (ord ge __THRESHOLD) then
      __UserWarning( S, ord, #K, PrintOut, true );
    end if; 

    gens := [];
    for X in OverGrp[1] do
      A := X^(2 @ T`Cat`Arrows);
      for Y in OverGrp[2] do
        B := Y^(1 @ T`Cat`Arrows);
        S_conj := [ A * s * Transpose(B) : s in S ];
        for Z in OverGrp[3] do
          C := Z^(0 @ T`Cat`Arrows);
          S_out := [ &+[ C[i][j]*S[i] : i in [1..#S] ] : j in [1..#S] ];
          if S_out eq S_conj then
            Append(~gens, DiagonalJoin(<A,B,C>));
          end if;
        end for;
      end for;
    end for;
    A := sub< GL(&+Dims,K) | gens >;
    A`DerivedFrom := < T, [2,1,0] >;
  end if;
  T`Bimap`Aut := A;
  return A;
end intrinsic;

// ==============================================================================
//                                     Groups
// ==============================================================================
// We include wrappers for p-class 2 groups.

// GrpPC
intrinsic IsometryGroup( G::GrpPC : DisplayStructure := true, Warning := true ) -> GrpMat
{Returns the isometry group of the finite p-class 2 group G.}
  require #FactoredOrder(G) eq 1 : "Must be a prime power group.";
  try
    T := pCentralTensor(G);
  catch err
    error "Cannot compute the p-central tensor.";
  end try;
  isom := IsometryGroup( T : DisplayStructure:=DisplayStructure, Warning:=Warning );
  return isom;
end intrinsic;

intrinsic PseudoIsometryGroup( G::GrpPC : Warning := true ) -> GrpMat
{Returns the pseudo-isometry group of the finite p-class 2 group G.}
  require #FactoredOrder(G) eq 1 : "Must be a prime power group.";
  try
    T := pCentralTensor(G);
  catch err
    error "Cannot compute the p-central tensor.";
  end try;
  pisom := PseudoIsometryGroup( T : Warning:=Warning );
  return pisom;
end intrinsic;

// GrpMat
intrinsic IsometryGroup( G::GrpMat : DisplayStructure := true, Warning := true ) -> GrpMat
{Returns the isometry group of the finite p-class 2 group G.}
  ord := Factorization(LMGOrder(G));
  require #ord eq 1 : "Must be a prime power group.";
  try
    T := pCentralTensor(G,ord[1][1],1,1);
  catch err
    error "Cannot compute the p-central tensor.";
  end try;
  isom := IsometryGroup( T : DisplayStructure:=DisplayStructure, Warning:=Warning );
  return isom;
end intrinsic;

intrinsic PseudoIsometryGroup( G::GrpMat : Warning := true ) -> GrpMat
{Returns the pseudo-isometry group of the finite p-class 2 group G.}
  ord := Factorization(LMGOrder(G));
  require #ord eq 1 : "Must be a prime power group.";
  try
    T := pCentralTensor(G,ord[1][1],1,1);
  catch err
    error "Cannot compute the p-central tensor.";
  end try;
  pisom := PseudoIsometryGroup( T : Warning:=Warning );
  return pisom;
end intrinsic;

// GrpPerm
intrinsic IsometryGroup( G::GrpPerm : DisplayStructure := true, Warning := true ) -> GrpMat
{Returns the isometry group of the finite p-class 2 group G.}
  require #FactoredOrder(G) eq 1 : "Must be a prime power group.";
  try
    T := pCentralTensor(G);
  catch err
    error "Cannot compute the p-central tensor.";
  end try;
  isom := IsometryGroup( T : DisplayStructure:=DisplayStructure, Warning:=Warning );
  return isom;
end intrinsic;

intrinsic PseudoIsometryGroup( G::GrpPerm : Warning := true ) -> GrpMat
{Returns the pseudo-isometry group of the finite p-class 2 group G.}
  require #FactoredOrder(G) eq 1 : "Must be a prime power group.";
  try
    T := pCentralTensor(G);
  catch err
    error "Cannot compute the p-central tensor.";
  end try;
  pisom := PseudoIsometryGroup( T : Warning:=Warning );
  return pisom;
end intrinsic;
