/* 
    Copyright 2016--2019 Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


/*
  This file contains all the definition of TenCat and its attributes.
*/


// -----------------------------------------------------------------------------
//                             Tensor space categories
// -----------------------------------------------------------------------------
declare type TenCat; 	
declare attributes TenCat : Arrows, Contra, Repeats, Symmetries, Valence;

/*
  Description of attributes:
    Arrows . . . . . . . . The function from Repeats to {-1,0,1} detailing which
                           spaces are dualized.
    Contra . . . . . . . . True/false whether the category is contravariant.
    Repeats. . . . . . . . A partition of {0..vav}.
    Symmetries . . . . . . The subgroup of Sym({0..vav}) which act on the 
                           coordinates as symmetries.
    Valence. . . . . . . . The valence vav + 1.
*/
