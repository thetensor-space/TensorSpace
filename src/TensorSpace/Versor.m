/*
    Copyright 2019 Joshua Maglione and James B. Wilson
    Provided under MIT License
*/

declare type VersorTenSpc : TenSpc;
declare attributes VersorTenSpc :
  Dom,    // Dom::TenSpc  . . . . Domain.
  Cod,    // Cod::TenSpc  . . . . Codomain.
  Contra; // Variance::Boolean  . true if contra-variant.


intrinsic VersorSpace( dom::TenSpc, cod::TenSpc ) -> VersorTenSpc
{Universal tensor space with free R-modules of given ranks and homotopism category.}
  
  return KTensorSpace( K, S, HomotopismCategory(#S) );
end intrinsic;

intrinsic 'in'()