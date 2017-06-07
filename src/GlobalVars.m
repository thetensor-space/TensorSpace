/* 
    Copyright 2016, 2017, Joshua Maglione, James B. Wilson.
    Distributed under GNU GPLv3.
*/


/*  Global variables  */
__VERSION := "1.1.1";
__SANITY_CHECK := false;
__LIST := { ModTupFld, ModFld, ModMatFld }; // suitable types we can do most computations with.
__FRAME := function( T ) // returns the 'domain' and the 'codomain'.
  if Type(T) eq TenSpcElt then
    return T`Domain cat [*T`Codomain*];
  else
    return T`Frame;
  end if;
end function;


/*  Verbose names  */
declare verbose eMAGma, 1; 
