/* 
    Copyright 2016--2019 Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


/*
  This file contains all the attributes associated to TenSpcElt.
  See 'src/TensorSpace/TenSpcType.m' for the definition of TenSpcElt. This also 
  contains definitions and attributes for the types associated to the in-fix 
  notation and the record format for bilinear maps (i.e. 3-tensors).
*/

// -----------------------------------------------------------------------------
//                                     Tensor
// -----------------------------------------------------------------------------
declare attributes TenSpcElt : Auto, Bimap, Cat, Codomain, Coerce, CoordImages, 
  Densor, Derivations, Domain, Element, FullyNondeg, Image, Map, Nondegenerate, 
  Parent, Permutation, Radicals, Reflexive, SymImage, Valence;

/* 
  Tensors will be thought of as multimaps internally but will be allowed 
  flexibility for the user.

  Description of attributes:
    Auto . . . . . . . . . The autotopism group of the tensor. 
    Bimap. . . . . . . . . The record of bimap info. Only defined when the 
                           valence is 3.
    Cat . . . . . . . . .  The tensor category.
    Codomain . . . . . . . The codomain of the tensor.
    Coerce . . . . . . . . If the tensor is created from some algebraic object,
                           this will contain maps to the modules.
    CoordImages. . . . . . The sequence of images of the coordinates.
    Densor . . . . . . . . The universal densor subspace of the tensor. 
    Derivations. . . . . . The list of sequences of tuples corresponding to a 
                           basis for derivations sorted by tuples of the form 
                           <A, k>, where A is a subset of {0..vav} of order at 
                           least 2 and k an integer in {2..#A}.
    Domain . . . . . . . . A list of the modules in the domain.
    Element. . . . . . . . The corresponding element in the tensor space.
    FullyNondeg. . . . . . The fully nondegenerate tensor.
    Image. . . . . . . . . The image of the tensor.
    Map. . . . . . . . . . The map from the domain into the codomain.
    Nondegenerate. . . . . A tuple containing the nondegenerate multimap and a 
                           homotopism to get there.
    Parent . . . . . . . . A tensor space which contains the tensor.
    Permutation. . . . . . Used for shuffling tensors. Allows for on-the-fly 
                           computations; defaults is Sym({1..vav})!1.
    Radicals . . . . . . . A list of the radicals for each Cartesian factor in 
                           the domain and the coradical.
    Reflexive. . . . . . . A record which states if the tensor is reflexive.
    SymImage . . . . . . . The indexed set of tuples <sigma, H> such that sigma 
                           is a generator of Symmetries and H in 
                           Hom(t, t^sigma). 
    Valence. . . . . . . . The number of modules in the frame.
*/


// -----------------------------------------------------------------------------
//                                  Bimap Spaces
// -----------------------------------------------------------------------------
declare type BmpU[BmpUElt];
declare type BmpV[BmpVElt];

declare attributes BmpU : Parent, Space;
declare attributes BmpV : Parent, Space;

/*
  Description of attributes:
    Parent . . . . . . . . The parent bimap.
    Space. . . . . . . . . The vector space U or V.
*/

declare attributes BmpUElt : Element, Parent;
declare attributes BmpVElt : Element, Parent;

/*
  Description of attributes:
    Element. . . . . . . . The element from the vector space U or V.
    Parent . . . . . . . . The parent space BmpU or BmpV.
*/

__RF_BIMAP := recformat< Adjoint : AlgMat, Aut : GrpMat, Isom : GrpMat, 
    PIsom : GrpMat, U : BmpU, V : BmpV >;

/*
  Bimap record:
    Adjoint. . . . . . . . The adjoint algebra from the StarAlg package.
    Aut. . . . . . . . . . The autotopism group.
    Isom . . . . . . . . . The isometry group.
    PIsom. . . . . . . . . The pseudo-isometry group.
    U. . . . . . . . . . . The BmpU space.
    V. . . . . . . . . . . The BmpV space.
*/

