/* 
    Copyright 2016--2019 Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


/*
  This file contains the definition and attributes for Hmtp.
*/

// -----------------------------------------------------------------------------
//                                   Homotopism
// -----------------------------------------------------------------------------
declare type Hmtp;
declare attributes Hmtp : Cat, Codomain, Domain, Kernel, Maps;

/* 
  Description of attributes:
    Cat. . . . . . . . . . The tensor category.
    Codomain . . . . . . . The tensor it maps into.
    Domain . . . . . . . . The tensor in the domain.
    Kernel . . . . . . . . The kernel of the homotopism.
    Maps . . . . . . . . . The list of maps from the spaces in the domain to the
                           spaces in the codomain.
                           Vn x ... x V1 >-> V0
                           |          |      |
                           Un x ... x U1 >-> U0 
                           The maps go in order from left to right.
*/
