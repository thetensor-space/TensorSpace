
// Construct a full rank matrix from K^d1 to K^d2  
__get_full_rank := function(K, d1, d2)
  I := IdentityMatrix(K, Minimum(d1, d2));
  if d1 ge d2 then
    M := VerticalJoin(I, ZeroMatrix(K, d1 - d2, d2));
  else
    M := HorizontalJoin(I, ZeroMatrix(K, d1, d2 - d1));
  end if;
  // '@' does not work with general Mtrx. This fixes that issue.
  return Hom(RSpace(K, d1), RSpace(K, d2))!M;
end function;

// get the function E by pre-composing t with the maps in M on coords A 
__get_eval_map := function(t, M, A)
  E := function(x)
    y := x;
    for i in [1..#x] do
      if #x-i in A then
        y[i] := x[i] @ M[i];
      end if;
    end for;
    if 0 notin A then
      return y @ t @ M[#M];
    else
      return y @ t;
    end if;
  end function;

  return E;
end function;

  /*
    Notes from JM: 

    Assumption is that f is "almost" a homotopism from t1 to t2. That is,
      t1 : U_v x ... x U_1 >-> U_0
           |           |       | 
      t2 : V_v x ... x V_1 >-> V_0,
    where the underlying tensor category of f places an orientation of the 
    edges above. 

    If a != 0, then we apply a shuffle to both t1 and t2, call them s1 and s2 
    respectively. We also need to apply the same permutation to f, call it g. 

    Now we need to define two more tensors, we will call them s1_g and s2_g. We
    define them based on g, and before we describe that, let me say a word about 
    arrow orientation. Running Arrows(TensorCategory(g)) will return a sequence
    in {-1, 1}. We assume 1 forces the arrow to point down, i.e. 
      g_a : U_a -> V_a
    and a -1 forces the arrow to point up:
      g_b : V_b -> U_b.
    Define a partition of {1, ..., v} as follows. Let A be the set of 
    coordinates whose arrows point up and B the arrows that point down. We have 
    a slight variation of this in the code, where the partition includes the 0.

    The two tensors we define will have the frame
      prod_{a in A} V_a x prod_{b in B} U_b  >->  C,
    where the domain is ordered properly, not necessarily grouped up in A and B,
    and C is U_0 if the last arrow is pointing up or V_0 if pointing down. 

    Now we build the corresponding (co)tensor spaces spanned by the mulitilinear
    forms. Like in previous builds, we check if they span the same subspace. If
    they do, then we can construct a lift: simply write the basis of one 
    subspace in terms of the other. If they do not span the same subspace, then 
    no such lift can be constructed. 
  */

// Input: s1::TenSpcElt, s2::TenSpcElt, g::Hmtp
// Output: BoolElt, Hmtp
__Lift_0_Coordinate := function(s1, s2, g)
  // initial setup
  K := BaseRing(s1);
  v := Valence(s1);
  M := Maps(g);

  // put the frames side-by-side
  F_zip := [*<Frame(s1)[i], Frame(s2)[i]> : i in [1..v]*];

  // map from {0, ..., v-1} to {-1, 1} giving arrow orientation
  Arr_map := TensorCategory(g)`Arrows;

  // map interpreting the output of Arr_map based on F_zip
  FindDom := map< {1,-1} -> {1,2} | [<1, 1>, <-1, 2>] >;

  // get partitions
  A := {a : a in {0..v-1} | a @ TensorCategory(g)`Arrows eq -1};
  B := {0..v-1} diff A;

  // put the final map in the list of mats
  if 0 in A then
    M[v] := __get_full_rank(K, Dimension(F_zip[v][1]), Dimension(F_zip[v][2]));
  else 
    M[v] := __get_full_rank(K, Dimension(F_zip[v][2]), Dimension(F_zip[v][1]));
  end if;

  // select the spaces described above
  // note the minus sign for the 0 coordinate!
  Fr := [*F_zip[i][(v - i) @ Arr_map @ FindDom] : i in [1..v-1]*] cat 
      [*F_zip[v][(-(0 @ Arr_map)) @ FindDom]*];
  
  // the maps
  eval1 := __get_eval_map(s1, M, A);
  eval2 := __get_eval_map(s2, M, B);
  
  // construct the tensors with all the data
  s1_g := Tensor(Fr, eval1, TensorCategory(g));
  s2_g := Tensor(Fr, eval2, TensorCategory(g));

  // construct the corresponding cotensor spaces
  S1 := AsCotensorSpace(s1_g)`Mod;
  S2 := AsCotensorSpace(s2_g)`Mod;

  // decide if we can lift
  if S1 ne S2 then
    return false, _;
  end if;

  // replace the dummy map with the correct map
  if 0 in A then
    M0 := Transpose(Matrix([Coordinates(S2, b) : b in Basis(S1)]));
  else
    M0 := Transpose(Matrix([Coordinates(S1, b) : b in Basis(S2)]));
  end if;
  M[v] := M0;

  // use pre-built machinery to build and verify
  check, H := IsHomotopism(s1, s2, M, TensorCategory(g));
  assert check;

  return true, H;
end function;


/* 
  Remark from PAB: this generalizes (and converts to homotopisms) the function
  
  IsIsotopism (T1::TenSpcElt, T2::TenSpcElt, L::Tup) -> BoolElt, GrpMatElt
  
  from "isom-test.m". This same function can also replace
  
  IsPseudoIsometry (T1::TenSpcElt, T2::TenSpcElt, g::GrpMatElt) -> BoolElt , GrpMatElt
  
  by making the input f have the same transformation in coordinates 2 and 1.
  The function Lift2 will be different in that regard. We will need a version tries
  to put the same transformation in the two missing coordinates.
*/

/*
  Input:
    (1) tensors t1 and t2 having compatible frames
    (2) f, an invertible map from the frame of t1 to the frame of t2;
        we further assume this map is passed as an isotopism between
        the 0-tensors on the given frames
    (3) a, an integer specifying a coordinate of the frames
  Output:
    (1) true if, and only if, f can modified to an isotopism g from t1
        to t2 by changing just the a-th coordinate
    (2) such an isotopism g 
*/
intrinsic InduceHomotopism(t1::TenSpcElt, t2::TenSpcElt, H::Hmtp, a::RngIntElt) 
  -> BoolElt, Hmtp
{Given tensors t1 and t2, a partial homotopism H between their frames, and a 
particular coordinate a, decide if a homotopism F from t1 to t2 exists such 
that F.b = H.b for all coordinates except a. If such a homotopism exists, it is 
returned.}

  // some checks to prevent garbage
  require Valence(t1) eq Valence(t2) : "Tensors do not have the same valence.";
  require a in {0..Valence(t1)-1} : "Unknown coordinate.";
  C1 := TensorCategory(t1);
  C2 := TensorCategory(t2);
  require {a} in RepeatPartition(C1) : "Given coordinate is fused.";
  require {a} in RepeatPartition(C2) : "Given coordinate is fused.";

  // construct a permutation
  v := Valence(t1);
  G := Sym({0..v-1});
  if a ne 0 then
    perm := G!(0, a);
  else
    perm := G!1;
  end if;

  // permute all the data
  s1 := Shuffle(t1, perm);
  s2 := Shuffle(t2, perm);
  H_shuf := Shuffle(H, perm);

  // run the magic
  check, F_shuf := __Lift_0_Coordinate(s1, s2, H_shuf);

  // interpret the output
  if not check then
    return false, _;
  end if;

  // Shuffle back
  F := Shuffle(F_shuf, perm^-1);
  another_check, F := IsHomotopism(t1, t2, Maps(F), TensorCategory(F));
  assert another_check;

  return true, F;
end intrinsic;
