/* 
    Copyright 2016--2019 Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


/*
  This file contains the attributes and record format associated to the 
  intrinsic 'DerivedFrom'.
*/


// -----------------------------------------------------------------------------
//                                 New Attributes
// -----------------------------------------------------------------------------
declare attributes GrpMat : DerivedFrom;
declare attributes AlgMat : DerivedFrom;
declare attributes AlgMatLie : DerivedFrom;
declare attributes ModMatFld : DerivedFrom;
declare attributes AlgGen : Star; 

/*
  Description of attributes:
    DerivedFrom. . . . . . The record of tensor information.
    Star . . . . . . . . . An involution on the algebra.
*/

__RF_DERIVED_FROM := recformat< Tensor : TenSpcElt, Coords : SetEnum, 
    Fused : BoolElt, RepCoords : SetEnum >;

/*
  DerivedFrom record:
    Tensor . . . . . . . . The tensor from where the object wsa derived from.
    Coords . . . . . . . . The corresponding coordinates for the blocks. 
    Fused. . . . . . . . . Whether or not the tensor category was incorporated.
    RepCoords. . . . . . . The set on which the object is representated on.
*/


// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

intrinsic DerivedFrom( ~X::., t::TenSpcElt, C::{RngIntElt}, RC::{RngIntElt}
  : Fused := true )
{This procedure stores the following tensor information to the object X. The 
tensor t, the corresponding coordinates C, the coordinates RC for which the 
object is represented on, and the string Type for the type of object X is.}
  require Type(X) in {AlgMat, AlgMatLie, GrpMat, ModMatFld} : 
    "No attribute to store tensor information.";
  R := rec< __RF_DERIVED_FROM | 
    Tensor := t, 
    Coords := C,
    Fused := Fused,
    RepCoords := RC
    >;
  X`DerivedFrom := R;
end intrinsic;
