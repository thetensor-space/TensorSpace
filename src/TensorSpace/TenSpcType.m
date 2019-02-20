/* 
    Copyright 2016--2019 Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


/*
  This file contains the definitions of TenSpc and TenSpcElt and the attributes 
  associated to TenSpc
*/

// -----------------------------------------------------------------------------
//                                  Tensor Space
// -----------------------------------------------------------------------------
declare type TenSpc[TenSpcElt]; // eventually inherit ModRng structure
declare attributes TenSpc : Cat, Coerce, Frame, Mod, Ring, UniMap, Valence;

/* 
  Description of attributes:
    Cat. . . . . . . . . . The category of the tensor space tensors.
    Coerce . . . . . . . . If the space is created from some algebraic object, 
                           this will contain maps to the modules.
    Frame. . . . . . . . . The sequence of the modules in the frame.
    Mod. . . . . . . . . . The R-submodule T.
    Ring . . . . . . . . . The base ring.
    UniMap . . . . . . . . The universal map: T -> hom(Va, ... hom(V1, V0) ...).
    Valence. . . . . . . . The valence of the space.
*/
