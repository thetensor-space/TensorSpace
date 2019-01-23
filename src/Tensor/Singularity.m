/* 
    Copyright 2019 Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


intrinsic Singularity( M::TenSpcElt, S::{RngIntElt} ) -> Sch
{Returns the T-singularities of the tensor as the scheme of the zero-locus of a set of polynomials.}
  v := M`Valence-1;
  require #S ne 0 and S subset {1..v} : "Set is not a nonempty subset of {1..v}.";
  T := { v-t+1 : t in S };
  try
    R := BaseRing( M );
  catch err
    error "Tensor does not have a base ring.";
  end try;
  require IsCommutative( R ) : "Base ring is not commutative.";
  D := M`Domain;
  T := Sort( {@ t : t in T @} );
  M_T := [* D[t] : t in T *];
  M_Tc := [* D[i] : i in {1..v} diff T *];
  X := [* Basis( M ) : M in M_T *];
  dims := [ Dimension( M ) : M in M_T ];
  consec_dims := [0] cat [ &+[ dims[i] : i in [1..j] ] : j in [1..#dims-1] ];
  I := CartesianProduct( < {1..#B} : B in X > );
  Y := CartesianProduct( < Basis(M) : M in M_Tc > );
  P := PolynomialRing( R, &+(dims) );
  polys := [];
  for y in Y do
    p := [ P!0 : i in [1..Dimension(M`Codomain)] ];
    for s in I do
      x := <>;
      j := 1;
      for i in [1..v] do
        if i in T then
          ind := Index(T,i);
          Append(~x,X[ind][s[ind]]);
        else
          Append(~x,y[j]);
          j +:= 1;
        end if;
      end for;
      mono := P!1; // monomial
      for i in [1..#s] do
        mono *:= P.(consec_dims[i] + s[i]);
      end for;
      xM := Coordinates( M`Codomain, x @ M );
      for i in [1..#xM] do
        p[i] +:= xM[i]*mono; 
      end for;
    end for;
    polys cat:= p;
  end for;
  // clean up
  polys := { p : p in polys };
  if P!0 in polys then
    Exclude(~polys, P!0);
  end if;
  I := ideal< P | polys >;
  S := Scheme(ProjectiveSpace( R, &+(dims)-1 ), Basis(I));
  return S;
end intrinsic;
