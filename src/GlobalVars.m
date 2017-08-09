/* 
    Copyright 2016, 2017, Joshua Maglione, James B. Wilson.
    Distributed under GNU GPLv3.
*/


/*  Global variables  */
__VERSION := "1.1.0";
__SANITY_CHECK := false;
__LIST := { ModTupFld, ModFld, ModMatFld }; // suitable types we can do most computations with.
__FRAME := function( T ) // returns the 'domain' and the 'codomain'.
  if Type(T) eq TenSpcElt then
    return T`Domain cat [*T`Codomain*];
  else
    return T`Frame;
  end if;
end function;
__FLAT := function( X ) 
  try 
    return Flat(X);
  catch err
    if Type(X) in {SetEnum, SetIndx} then
      return $$([x : x in X]);
    end if;
  end try;
  return X;
end function;


/*  Verbose names  */
declare verbose eMAGma, 1; 
