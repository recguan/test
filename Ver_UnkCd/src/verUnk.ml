open AbdSemantic
open EntAbd
open List
open Semantic
open Type
open Utils

(* Assign program variables with corersponding special variables *)
let rec assign_svar_plist vars =
  match vars with
    | [] -> []
    | (Var v)::vs -> (Eq(Var v, SVar v))::(assign_svar_plist vs)
    | _::vs -> assign_svar_plist vs

let assign_svar vars = SH(assign_svar_plist vars, [])

let rec assign_old_svar_plist vars =
  match vars with
    | [] -> []
    | (Var v)::vs -> (Eq(Var v, SVar ("old"^v)))::(assign_old_svar_plist vs)
    | _::vs -> assign_old_svar_plist vs

let assign_old_svar vars = SH(assign_old_svar_plist vars, [])

(* gen_svar_old_pairs generates pairs of (svar y, var oldy) for a list of substitutions *)
let rec gen_svar_old_pairs vars =
  match vars with
    | [] -> []
    | (Var v)::vs -> (SVar ("old"^v), Var ("old"^v))::(gen_svar_old_pairs vs)
    | _::vs -> gen_svar_old_pairs vs

(* trans_var_to_svar transforms a list of vars to corr svars *)
let rec trans_var_to_svar vars =
  match vars with
    | [] -> []
    | (Var v)::vs -> (SVar v)::(trans_var_to_svar vs)
    | (SVar v)::vs -> (SVar v)::(trans_var_to_svar vs)
    | _::vs -> trans_var_to_svar vs

let rec trans_var_to_old_svar vars =
  match vars with
    | [] -> []
    | (Var v)::vs -> (SVar ("old"^v))::(trans_var_to_old_svar vs)
    | _::vs -> trans_var_to_svar vs

(* All reachable expressions from elist. res should be [] init. *)
let rec reach_exp plist slist elist res =
  match elist with
    | [] -> res
    | e::es -> let sp = find_aliased_head e plist slist in
        match sp with
          | Lseg(e_1, e_2) ->
              if mem e_1 res then reach_exp plist slist es res
              else reach_exp plist slist (e_2::es) (e_1::res)
          | Point(e_1, e_2) ->
              if mem e_1 res then reach_exp plist slist es res
              else reach_exp plist slist (e_2::es) (e_1::res)
          | _ -> reach_exp plist slist es res

let reach_var hp elist =
  if hp = Top then [] else reach_exp (pure_part hp) (sep_part hp) elist []

(* Local *)
let local (SH(plist, slist)) elist =
  let reach_es = reach_exp plist slist elist [] in
  let find_aliased_head_temp plist slist e = find_aliased_head e plist slist in
    let reach_sep = map (find_aliased_head_temp plist slist) reach_es in
      SH(plist, reach_sep)

(* Frame *)
let frame (SH(plist, slist)) elist =
  let SH(plist, reach_sep) = local (SH(plist, slist)) elist in
    SH(plist, fold_left elim_lst_ele slist reach_sep)

(* abduct: d against post to strengthen (d, m) *)
let abduct post (d, m) =
  let (frm, abd) = ent_abd d post in
    (merge_heap d abd, merge_heap m abd)

(* merge_pre *)
let merge_pre b (pre,post) = (merge_heap (SH(b,[])) pre, post)

(* Below instantiates the special variables in specs to be program variables *)
let svar_to_var e =
  match e with
    | SVar v -> if (map (String.contains v) ['o';'l';'d']) = [true; true; true] then SVar v else Var v
    | e -> e

let rec plist_to_var pl =
  match pl with
    | [] -> []
    | (Eq(SVar v_1, Var v_2))::ps -> if v_1 = v_2 then (Eq(SVar v_1, Var v_2))::(plist_to_var ps) else (Eq(Var v_1, Var v_2))::(plist_to_var ps)
    | (Eq(Var v_1, SVar v_2))::ps -> if v_1 = v_2 then (Eq(Var v_1, SVar v_2))::(plist_to_var ps) else (Eq(Var v_1, Var v_2))::(plist_to_var ps)
    | (Eq(e_1, e_2))::ps -> (Eq(svar_to_var e_1, svar_to_var e_2))::(plist_to_var ps)
    | (Neq(e_1, e_2))::ps -> (Neq(svar_to_var e_1, svar_to_var e_2))::(plist_to_var ps)
    | PTop::ps -> PTop::(plist_to_var ps)

let rec slist_to_var sl =
  match sl with
    | [] -> []
    | (Point(e_1, e_2))::ss -> (Point(svar_to_var e_1, svar_to_var e_2))::(slist_to_var ss)
    | (Lseg(e_1, e_2))::ss -> (Lseg(svar_to_var e_1, svar_to_var e_2))::(slist_to_var ss)
    | s::ss -> s::(slist_to_var ss)

let heap_to_var (SH(pl, sl)) = SH(plist_to_var pl, slist_to_var sl)

let heap_pair_to_var (hp_1, hp_2) = (heap_to_var hp_1, heap_to_var hp_2)
(* Above instantiates the special variables in specs to be program variables *)

(* test_reach: for (d,m), test whether fv(m) \subseteq reach(d, a&b) *)
let test_reach vs (d, m) =
  let reach_d = reach_var d (trans_var_to_svar vs) in
  let vars_m = vars_in [] (sep_part m) [] in
  let svars_m = svars_in [] (sep_part m) [] in
    contained_in (vars_m @ svars_m) reach_d

(* verify_single_specv_c2: processes the foreach D_1 \in S_1 do *)
let rec verify_single_specv_c2 u xs ys c_2 x0s y0s post d_1 =
  let vs = xs @ ys in
    let pure_svar = assign_svar vs in
      let flvar_y_pairs = combine (map fresh_logical ys) ys in
        let s_2 = abd_semantic c_2 [(merge_heap (fold_left pair_subst (frame d_1 vs) flvar_y_pairs) pure_svar, pure_svar)] in
          let s_3 = map (abduct (fold_left pair_subst post (gen_svar_old_pairs y0s))) s_2 in
            if mem false (map (test_reach (nub ((trans_var_to_svar (xs @ ys @ x0s @ y0s)) @ (trans_var_to_old_svar y0s)))) s_3) then [(Top,Top)]
            else make_pair [fold_left pair_subst (local d_1 vs) (combine (trans_var_to_svar vs) vs)] (map snd s_3)

(* verify_single_specv: computer S_1 = |[C_1]| (Pre & y0=c) *)
(* TODO: investigate assign_svar to see whether y0s=oldy0s is needed here *)
let rec verify_single_specv (c_1, u, xs, ys, c_2, x0s, y0s) (pre, post) =
  let s_1 = semantic c_1 [merge_heap (assign_old_svar y0s) pre] in
    if mem Top s_1 then [(Top,Top)] else nub (flatten (map (verify_single_specv_c2 u xs ys c_2 x0s y0s post) s_1))

let restore_pre_from_var_to_svar vs (pre, post) =
  (fold_left pair_subst pre (combine (trans_var_to_svar vs) vs), post)

(* AllSpec is omitted because we require each function call bring its pre and post in actual parameters.
   pre_v and post_v are pre and post for the first 7-tuple (of type unkseg).
   This function returns a list of name * heap * heap as the unknowns' specs. *)
let rec verify (c_1, u, xs, ys, c_2, x0s, y0s) spec_v =
  let spec_u = nub (flatten (map (verify_single_specv (c_1, u, xs, ys, c_2, x0s, y0s)) spec_v)) in
    if mem (Top,Top) spec_u then [("Top",[(Top,Top)])]
    else case_analysis (map heap_pair_to_var spec_u) u
and case_analysis spec_u u =
  match u with
    | UnkFun(n, xs, ys) -> [(n, map (restore_pre_from_var_to_svar (xs @ ys)) spec_u)]
    | If_l(b, V(c_1,u_1,xs,ys,c_2,x0s,y0s), c) -> verify (c_1,u_1,xs,ys,c_2,x0s,y0s) (filter check_consist_heap_pair (map (merge_pre [b]) spec_u))
    | If_r(b, c, V(c_1,u_1,xs,ys,c_2,x0s,y0s)) -> verify (c_1,u_1,xs,ys,c_2,x0s,y0s) (filter check_consist_heap_pair (map (merge_pre [pure_not b]) spec_u))
    | If_b(b, V(c_1_1,u_1,xs_1,ys_1,c_2_1,x0s_1,y0s_1), V(c_1_2,u_2,xs_2,ys_2,c_2_2,x0s_2,y0s_2)) -> (verify (c_1_1,u_1,xs_1,ys_1,c_2_1,x0s_1,y0s_1) (filter check_consist_heap_pair (map (merge_pre [b]) spec_u))) @ (verify (c_1_2,u_2,xs_2,ys_2,c_2_2,x0s_2,y0s_2) (filter check_consist_heap_pair (map (merge_pre [pure_not b]) spec_u)))

(*

print_float (Sys.time()); let v=

> Test case 1:

proc findLast(; x) {
  w := [x];
  if w = null then skip
  else foo(w; x); findLast(; x) fi
}

let c_1 = Atom(Assign(Var"w", Ref(Var"x")));;
let u = If_r (Eq(Var"w",Nil), Atom(Skip), V(Atom(Skip), UnkFun("foo", [Var"w"], [Var"x"]), [Var"w"], [Var"x"], Fun ("fT",[],[Var"x"], SH([Neq(Var"x",Nil)],[Lseg(Var"x",Nil)]), SH([],[Lseg(Var"oldx",Var"x");Point(Var"x",Nil)])), [], [Var"x"]));;
let xs = [Var"w"];;
let ys = [Var"x"];;
let c_2 = Atom(Skip);;
let x0s = [];;
let y0s = [Var"x"];;
verify (c_1, u, xs, ys, c_2, x0s, y0s) [(SH([Neq(Var"x",Nil)],[Lseg(Var"x",Nil)]), SH([],[Lseg(Var"oldx",Var"x");Point(Var"x",Nil)]))];;


> Test case 2:

proc findLast(w, x; y, z) {
  w := [x];
  if w = null then z = x
  else foo(x; y); findLast(y; z) fi
}

let c_1 = Atom(Assign(Var"w", Ref(Var"x")));;
let u = If_r (Eq(Var"w",Nil), Seq[Atom(Assign(Var"z", Var"x")); Atom(Assert(SH([],[])))], V(Atom(Assert(SH([],[]))), UnkFun("foo", [Var"x"], [Var"y"]), [Var"x"], [Var"y"], Seq[Atom(Assert(SH([],[]))); Fun ("fT",[Var"y"],[Var"z"], SH([Neq(Var"y",Nil)],[Lseg(Var"y",Nil)]), SH([],[Lseg(Var"y",Var"z");Point(Var"z",Nil)])); Atom(Assert(SH([],[])))], [Var"w";Var"x"], [Var"y";Var"z"]));;
let xs = [Var"x"];;
let ys = [Var"y"];;
let c_2 = Atom(Skip);;
let x0s = [Var"w";Var"x"];;
let y0s = [Var"y";Var"z"];;
verify (c_1, u, xs, ys, c_2, x0s, y0s) [(SH([Neq(Var"x",Nil)],[Lseg(Var"x",Nil)]), SH([],[Lseg(Var"x",Var"z");Point(Var"z",Nil)]))];;


> Test case 3:

let c_1 = Atom(Assign(Var"w", Ref(Var"x")));;
let c_2 = Seq [Fun("app",[Var"z"],[Var"y"], SH([],[Lseg(Var"y",Nil);Lseg(Var"z",Nil)]), SH([],[Lseg(Var"oldy",Nil)])); Fun("app",[Var"y"],[Var"x"], SH([],[Lseg(Var"x",Nil);Lseg(Var"y",Nil)]), SH([],[Lseg(Var"oldx",Nil)]))];;
let v_3 = V(Seq[Fun("app",[Var"z"],[Var"u"], SH([],[Lseg(Var"u",Nil);Lseg(Var"z",Nil)]), SH([],[Lseg(Var"oldu",Nil)]))], UnkFun("foo", [Var"x";Var"y"],[]), [Var"x";Var"y"],[], Atom(Skip), [Var"x";Var"y";Var"z"], [Var"u"]);;
let v_4 = V(Atom(Skip), UnkFun("foo", [Var"x";Var"z"],[]), [Var"x";Var"z"],[], Atom(Skip), [Var"x";Var"z"],[]);;
let u_2 = If_b (Neq(Var"u",Nil), v_3, v_4);;
let u_1 = If_r (Eq(Var"w",Nil), c_2, V(Atom(Assign(Var"u",Ref(Var"y"))), u_2, [Var"x";Var"y";Var"z"], [Var"u"], Atom(Skip), [Var"x";Var"y";Var"z"], [Var"u"]));;
let xs = [Var"w";Var"x";Var"y";Var"z"];;
let ys = [Var"r";Var"u"];;
let c_2 = Atom(Skip);;
let x0s = [Var"w";Var"x";Var"y";Var"z"];;
let y0s = [Var"r";Var"u"];;
verify (c_1, u_1, xs, ys, c_2, x0s, y0s) [(SH([Neq(Var"x",Nil);Neq(Var"y",Nil)],[Lseg(Var"x",Nil);Lseg(Var"y",Nil);Lseg(Var"z",Nil)]), SH([Neq(Var"x",Nil)],[Lseg(Var"x",Nil)]))];;


> Test case 4:

// ls(x, null) * ls(y, null)
proc append (y; x) {
  if x = null then x := y
  else
    w := [x]; // unknown(x; w);
    if w = null then [x] := y
    else append(y; w)
    fi
  fi
}
// ls(x, y) * ls(y, null)

                If(Eq(Var"w",Nil),
                   Atom(Assign(Ref(Var"x"),Var"y")),
                   Fun("append",[Var"y"],[Var"w"],
                       SH([],[Lseg(Var"w",Nil);Lseg(Var"y",Nil)]),
                       SH([],[Lseg(Var"w",Var"y");Lseg(Var"y",Nil)])
                      )
                  ),

let c_1 = Atom(Skip);;
let u = If_r (Eq(Var"x",Nil),
              Seq[Atom(Assign(Var"x", Var"y")); Atom(Assert(SH([],[])))],
              V(Atom(Assert(SH([],[]))),
                UnkFun("foo", [Var"x"], [Var"w"]), [Var"x"], [Var"w"],
                   Fun("append",[Var"y"],[Var"w"],
                       SH([],[Lseg(Var"w",Nil);Lseg(Var"y",Nil)]),
                       SH([],[Lseg(Var"w",Var"y");Lseg(Var"y",Nil)])
                      ),
                [Var"y"],[Var"w";Var"x"]
               )
             );;
let xs = [Var"y"];;
let ys = [Var"x";Var"w"];;
let c_2 = Atom(Skip);;
let x0s = [Var"y"];;
let y0s = [Var"x";Var"w"];;
verify (c_1, u, xs, ys, c_2, x0s, y0s) [(SH([],[Lseg(Var"x",Nil);Lseg(Var"y",Nil)]), SH([],[Lseg(Var"x",Var"y");Lseg(Var"y",Nil)]))];;


> Test case 5:

// ls(x, null)
proc copy(x; y) {
  if x = null then y := null
  else
    w := [x];
    copy (w; y);
    z := new(); // unknown(; y);
    [z] := y;   // unknown(; y);
    y := z      // unknown(; y);
    // Or directly y := new(y) // unknown(; y);
  fi
}
// ls(x, null) * ls(y, null)

let c_1 = Atom(Skip);;
let u = If_r (Eq(Var"x",Nil),
              Seq[Atom(Assign(Var"y", Nil)); Atom(Assert(SH([],[])))],
              V(Atom(Assert(SH([],[]))),
                UnkFun("foo", [Var"x"], [Var"w"]), [Var"x"], [Var"w"],
                   Fun("append",[Var"y"],[Var"w"],
                       SH([],[Lseg(Var"w",Nil);Lseg(Var"y",Nil)]),
                       SH([],[Lseg(Var"w",Var"y");Lseg(Var"y",Nil)])
                      ),
                [Var"y"],[Var"w";Var"x"]
               )
             );;
let xs = [Var"y"];;
let ys = [Var"x";Var"w"];;
let c_2 = Atom(Skip);;
let x0s = [Var"y"];;
let y0s = [Var"x";Var"w"];;
verify (c_1, u, xs, ys, c_2, x0s, y0s) [(SH([],[Lseg(Var"x",Nil);Lseg(Var"y",Nil)]), SH([],[Lseg(Var"x",Var"y");Lseg(Var"y",Nil)]))];;


> Test case 6:

// ls(x, null)
proc revCopy(x; y) {
  if x = null then skip
  else
    z := new(); // unknown(; y);
    [z] := y;   // unknown(; y);
    y := z;     // unknown(; y);
    // Or directly y := new(y); // unknown(; y);
    w := [x];
    revCopy (w; y)
  fi
}
// ls(x, null) * ls(y, old(y))

let c_1 = Atom(Skip);;
let u = If_r (Eq(Var"x",Nil),
              Atom(Skip),
              V(Atom(Assert(SH([],[]))),
                UnkFun("foo", [], [Var"y"]), [], [Var"y"],
                Seq [Atom(Assign(Var"w",Ref(Var"x")));
                   Fun("revCopy",[Var"w"],[Var"y"],
                       SH([],[Lseg(Var"w",Nil)]),
                       SH([],[Lseg(Var"w",Nil)])
                      )],
                [Var"y"],[Var"w";Var"x"]
               )
             );;
let xs = [Var"x"];;
let ys = [Var"y";Var"w"];;
let c_2 = Atom(Skip);;
let x0s = [Var"x"];;
let y0s = [Var"y";Var"w"];;
verify (c_1, u, xs, ys, c_2, x0s, y0s) [(SH([],[Lseg(Var"x",Nil)]), SH([],[Lseg(Var"x",Nil)]))];;


> Test case 7:

// ls(x, null)
proc clear(; x) {
  if x = null then skip
  else
    w := [x];
    dispose(x,w); // unknown(x,w; );
    x := w;
    clear(; x)
  fi
}
// emp & x = null

let c_1 = Atom(Skip);;
let u = If_r (Eq(Var"x",Nil),
              Atom(Skip),
              V(Atom(Assign(Var"w",Ref(Var"x"))),
                UnkFun("foo", [], [Var"x";Var"w"]), [], [Var"x";Var"w"],
                Seq [Atom(Assign(Var"x",Var"w"));
                   Fun("clear",[],[Var"x"],
                       SH([],[Lseg(Var"x",Nil)]),
                       SH([Eq(Var"x",Nil)],[])
                      )],
                [],[Var"w";Var"x"]
               )
             );;
let xs = [];;
let ys = [Var"x";Var"w"];;
let c_2 = Atom(Skip);;
let x0s = [];;
let y0s = [Var"x";Var"w"];;
verify (c_1, u, xs, ys, c_2, x0s, y0s) [(SH([],[Lseg(Var"x",Nil)]), SH([Eq(Var"x",Nil)],[]))];;


> Other sub test cases:

let pre = SH([Neq(Var"x",Nil)],[Lseg(Var"x",Nil)]);;
let post = SH([],[Lseg(Var"oldx",Var"x");Point(Var"x",Nil)]);;

let spec_u = verify_single_specv (c_1, u, xs, ys, c_2, x0s, y0s) (pre, post);;
let spec_u = map heap_pair_to_var spec_u;;
let spec_u = filter check_consist_heap_pair (map (merge_pre [Neq(Var"w",Nil)]) spec_u);;


let c_1 = Atom(Skip);;
let u = UnkFun("foo", [Var"w"], [Var"x"]);;
let xs = [Var"w"];;
let ys = [Var"x"];;
let c_2 = Fun ("fT",[],[Var"x"], SH([Neq(Var"x",Nil)],[Lseg(Var"x",Nil)]),
SH([],[Lseg(Var"oldx",Var"x");Point(Var"x",Nil)]));;
let x0s = [Var"w"];;
let y0s = [Var"x"];;

let pre = fst (hd spec_u);;
let post = snd (hd spec_u);;



let s_1 = semantic c_1 [merge_heap (assign_old_svar y0s) pre];;
let d_1 = hd s_1;;
let vs = xs @ ys;;
let pure_svar = assign_svar vs;;
let flvar_y_pairs = combine (map fresh_logical ys) ys;;
let s_2 = abd_semantic c_2 [(merge_heap (fold_left pair_subst (frame d_1 vs) flvar_y_pairs) pure_svar, pure_svar)];;
let s_3 = map (abduct (fold_left pair_subst post (gen_svar_old_pairs y0s))) s_2;;
let vvv = (nub ((trans_var_to_svar (xs @ ys @ x0s @ y0s)) @ (trans_var_to_old_svar y0s)));;
let (ddd, mmm) = hd s_3;;



verify (c_1, u, xs, ys, c_2, x0s, y0s) [(SH([Neq(Var"x",Nil)],[Lseg(Var"x",Nil)]), SH([],[Lseg(Var"oldx",Var"x");Point(Var"x",Nil)]))];;



let c_1 = Atom(Skip);;
let u = UnkFun("foo", [Var"x"], []);;
let xs = [Var"x"];;
let ys = [];;
let c_2 = Atom(Skip);;
let x0s = [Var"x";Var"y"];;
let y0s = [];;
verify (c_1, u, xs, ys, c_2, x0s, y0s) [(SH([],[Lseg(Var"x",Nil);Lseg(Var"y",Nil)]), SH([],[Lseg(Var"x",Nil);Lseg(Var"y",Nil)]))];;


*)
