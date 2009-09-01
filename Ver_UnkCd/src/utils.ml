open List
open Type

(* Fresh logical variable *)

let ref_global = ref 10000;;

let rec fresh_logical va =
  match va with
    | Var s -> ref_global := !ref_global + 1; LVar (s ^ "_" ^ (string_of_int !ref_global))
    | LVar s -> ref_global := !ref_global + 1; LVar (s ^ "_" ^ (string_of_int !ref_global))
    | SVar s -> ref_global := !ref_global + 1; LVar (s ^ "_" ^ (string_of_int !ref_global))
    | Ref e -> fresh_logical e
    | Nil -> Nil

(* flvar_for_old_pairs takes pairs (flv, y) and gives (flv, oldy). It is used for call-by-ref vars in a function call *)
let rec flvar_for_old_pairs flvar_y_pairs =
  match flvar_y_pairs with
    | [] -> []
    | (LVar lv, Var v)::pairs -> (LVar lv, Var ("old"^v))::(flvar_for_old_pairs pairs)

(******)
(* Nub (duplicate removal) *)
let add_elem x xlist = if mem x xlist then xlist else x::xlist
let nub xlist = fold_right add_elem xlist []
(* nub [3;1;4;1;5;9;2;6;5;3;5;8;9;7;9];; *)

(******)
(* Eliminate an element from a list *)
let elim_lst_ele mylist ele =
  let is_not e = e <> ele in
    filter is_not mylist

(******)
(* Test whether one list is contained in another *)
let rec contained_in list_1 list_2 =
  match list_1 with
    | [] -> true
    | e::es -> if mem e list_2 then contained_in es list_2 else false
(* contained_in [3;1;4;1;5;9;2;7] [3;1;4;1;5;9;2;6;5;3;5;8;9;7;9];; *)

(******)
let pure_not b =
  match b with
    | Eq(e_1,e_2) -> Neq(e_1,e_2)
    | Neq(e_1,e_2) -> Eq(e_1,e_2)
    | PTop -> PTop


(******)
(* Subst [e_1/e_2] e *)

(* esub substitutes within an expression *)
let rec esub e_1 e_2 e =
  match (e_2, e) with
    | (Var v_2, Var v) -> if v_2 = v then e_1 else e
    | (LVar lv_2, LVar lv) -> if lv_2 = lv then e_1 else e
    | (SVar sv_2, SVar sv) -> if sv_2 = sv then e_1 else e
    | (_, Ref e) -> Ref (esub e_1 e_2 e)
    | (_, _) -> e

(* psub substitutes within one pure formula; for a list use map *)
let rec psub e_1 e_2 pure_e =
  match pure_e with
    | Eq (e_3, e_4) -> Eq (esub e_1 e_2 e_3, esub e_1 e_2 e_4)
    | Neq (e_3, e_4) -> Neq (esub e_1 e_2 e_3, esub e_1 e_2 e_4)
    | _ -> pure_e

(* ssub substitutes within a separation formula *)
let rec ssub e_1 e_2 sep_e =
  match sep_e with
    | Lseg (e_3, e_4) -> Lseg (esub e_1 e_2 e_3, esub e_1 e_2 e_4)
    | Point (e_3, e_4) -> Point (esub e_1 e_2 e_3, esub e_1 e_2 e_4)
    | _ -> sep_e

(* subst (LVar "x1") (Var "x") (SH([Eq(Var"y", Var"x"); Neq(Var"x", Var"z"); Eq(Var"x", LVar"x0"); Eq(Var"z", LVar"z1")], [Lseg(Var"x", Nil); Point(Var"z", Var"y")]));; *)
let subst e_1 e_2 hp =
  match hp with
    | Top -> Top
    | SH(plist, slist) -> SH(map (psub e_1 e_2) plist, map (ssub e_1 e_2) slist)

(* For mapping to a list of subst pairs *)
let pair_subst hp (e_1, e_2) = subst e_1 e_2 hp


(******)
let fst (a, b) = a
let snd (a, b) = b

(******)
(* pure_part takes the pure part of a heap *)
let pure_part hp =
  match hp with
    | SH(pl, sl) -> pl
    | Top -> [PTop]

(******)
(* sep_part takes the sep part of a heap *)
let sep_part hp =
  match hp with
    | SH(pl, sl) -> sl
    | Top -> [STop]

(******)
(* make_pair makes a catesian product of two (arbitary) lists. *)
let rec make_pair pls sls =
  match (pls, sls) with
    | (_, []) -> []
    | ([], sl::sls) -> []
    | (pl::pls, sl::sls) -> (pl, sl)::(make_pair [pl] sls) @ (make_pair pls (sl::sls))
(* make_pair [1;2] [3;4];; *)

(******)
(* make_heap_pair makes a list of heap pairs with catesian product of lists pls and sls. *)
let rec make_heap_pair pls sls =
  match (pls, sls) with
    | ([], []) -> []
    | (pl::pls, []) -> []
    | ([], sl::sls) -> []
    | (pl::pls, sl::sls) -> (SH (pl, sl))::(make_heap_pair [pl] sls) @ (make_heap_pair pls (sl::sls))


(******)
(* Find all variable aliases of E:exp (sometimes we can use this to partly simulate entailment)
   The pure list must be consistent without Eq(a,b) and Neq(a,b) at the same time *)

let rec find_direct_alias e plist =
  match (e, plist) with
    | (e_1, []) -> [e_1]
    | (e_1, (Eq (e_2, e_3))::ps) ->
        if (e_1 = e_2) then
          e_3::(find_direct_alias e_1 ps)
        else if (e_1 = e_3) then
          e_2::(find_direct_alias e_1 ps)
        else
          find_direct_alias e_1 ps
    | (e_1, p::ps) -> find_direct_alias e_1 ps

let rec find_direct_alias_list elist plist =
  match elist with
    | [] -> []
    | e::es -> (find_direct_alias e plist) @ (find_direct_alias_list es plist)

let rec find_alias_list elist plist =
  let alist = nub (find_direct_alias_list elist plist) in
    if length elist < length alist then
      find_alias_list alist plist
    else
      alist

(* find_alias finds all the aliases of exp e in a purelist *)
(* find_alias (Var "x") [Eq(Var"x",LVar"x_1"); Eq(LVar"x_1",LVar"x_2"); Neq(LVar"x_1",LVar"x_3"); Neq(LVar"x_1",Var"y"); Eq(LVar"x_4",LVar"x_1"); Eq(LVar"x_4",LVar"x_5")];; *)
let find_alias e plist = find_alias_list [e] plist


(******)
(* vars_in, lvars_in, svars_in: Vars, LVars, SVars *)
let rec vars_in_explist elist =
  match elist with
    | [] -> []
    | (Var v)::es -> (Var v)::(vars_in_explist es)
    | (Ref r)::es -> vars_in_explist (r::es)
    | e::es -> vars_in_explist es

let rec lvars_in_explist elist =
  match elist with
    | [] -> []
    | (LVar v)::es -> (LVar v)::(lvars_in_explist es)
    | (Ref r)::es -> lvars_in_explist (r::es)
    | e::es -> lvars_in_explist es

let rec svars_in_explist elist =
  match elist with
    | [] -> []
    | (SVar v)::es -> (SVar v)::(svars_in_explist es)
    | (Ref r)::es -> svars_in_explist (r::es)
    | e::es -> svars_in_explist es

let rec exps_in_purelist plist =
  match plist with
    | [] -> []
    | (Eq(e_1,e_2))::ps -> e_1::e_2::(exps_in_purelist ps)
    | (Neq(e_1,e_2))::ps -> e_1::e_2::(exps_in_purelist ps)
    | p::ps -> exps_in_purelist ps

let rec exps_in_seplist slist =
  match slist with
    | [] -> []
    | (Point(e_1,e_2))::ss -> e_1::e_2::(exps_in_seplist ss)
    | (Lseg(e_1,e_2))::ss -> e_1::e_2::(exps_in_seplist ss)
    | s::ss -> exps_in_seplist ss

let vars_in plist slist elist =
  let pureexp = exps_in_purelist plist in
  let sepexp = exps_in_seplist slist in
    nub (vars_in_explist (pureexp @ sepexp @ elist))

let lvars_in plist slist elist =
  let pureexp = exps_in_purelist plist in
  let sepexp = exps_in_seplist slist in
    nub (lvars_in_explist (pureexp @ sepexp @ elist))

let svars_in plist slist elist =
  let pureexp = exps_in_purelist plist in
  let sepexp = exps_in_seplist slist in
    nub (svars_in_explist (pureexp @ sepexp @ elist))
(* vars_in [Eq(Var"x",LVar"x_1");Eq(LVar"x_2",LVar"x_1");Eq(Var"y",LVar"y_1");Eq(LVar"y_1",LVar"y_2");Eq(Var"z",Nil)] [Lseg(LVar"x_1",Var"y");Point(LVar"y_1",Nil)] [Var"z";LVar"z_1";SVar"a"];; *)


(* find_head_in_heap finds a point-to or lseg with head e in splist *)
(* find_head_in_heap (LVar"x_1") [Lseg(Var"y",Nil); Lseg(LVar"x_1",Nil)];; *)
let rec find_head_in_heap e splist =
  match splist with
    | [] -> Emp
    | s::ss ->
        match s with
          | Point (e_1, e_2) ->
              if e = e_1 then Point (e_1, e_2) else find_head_in_heap e ss
          | Lseg (e_1, e_2) ->
              if e = e_1 then Lseg(e_1, e_2) else find_head_in_heap e ss
          | s -> find_head_in_heap e ss

(* find_head_from_list finds any point-to or lseg with head from any alias in es *)
(* find_head_from_list [Var"x"; LVar"x_1"] [Lseg(Var"y",Nil); Lseg(LVar"x_1",Nil)];; *)
let rec find_head_from_list es splist =
  match es with
    | [] -> Emp
    | e::es ->
        let sp = find_head_in_heap e splist in
          if sp <> Emp then sp else find_head_from_list es splist

(* find_aliased_head finds a possible separation formula (lseg or point-to)
   whose head is an alias of e, by combining find_alias and find_head_from_list *)
let find_aliased_head e plist slist = find_head_from_list (find_alias e plist) slist
(* find_aliased_head (Var"x") [Eq(Var"x",Var"y"); Eq(LVar"y_1",Var"y"); Neq(Var"z",LVar"y_1")] [Lseg(LVar"y_1",Nil)];; *)


(* The tail series corresponding to the above three *)
let rec find_tail_in_heap e splist =
  match splist with
    | [] -> Emp
    | s::ss ->
        match s with
          | Point (e_1, e_2) ->
              if e = e_2 then Point (e_1, e_2) else find_tail_in_heap e ss
          | Lseg (e_1, e_2) ->
              if e = e_2 then Lseg(e_1, e_2) else find_tail_in_heap e ss
          | s -> find_tail_in_heap e ss

let rec find_tail_from_list es splist =
  match es with
    | [] -> Emp
    | e::es ->
        let sp = find_tail_in_heap e splist in
          if sp <> Emp then sp else find_tail_from_list es splist

let find_aliased_tail e plist slist = find_tail_from_list (find_alias e plist) slist
(* find_aliased_tail (Var"x") [Eq(Var"x",Var"y"); Eq(LVar"y_1",Var"y"); Neq(Var"z",LVar"y_1")] [Point(Var"z",Var"y"); Lseg(LVar"y_1",Nil)];; *)


(* test_neq takes a pure list of eqs and neqs, and a list of alias pairs *)
(* (for each pair, the first is an alias of e_1 and the second e_2). *)
(* If any pair of alias to (e_1,e_2) is in Neq, then return true; *)
(* otherwise return false (Eq or not known). Used by judge_neq. *)
let rec test_neq plist a_pairs =
  match a_pairs with
    | [] -> false
    | (e_1, e_2)::aps ->
        if (mem (Neq(e_1, e_2)) plist) || (mem (Neq(e_2, e_1)) plist) then true
        else test_neq plist aps

(* judge_neq judges e_1 \neq e_2 or not; if we have their aliases are not equal, *)
(* then true; otherwise (they are equal or we don't know) just false. *)
let judge_neq plist e_1 e_2 =
  let alias_1 = find_alias e_1 plist in
    if mem e_2 alias_1 then false else
      let alias_2 = find_alias e_2 plist in
        let a_pairs = make_pair alias_1 alias_2 in
          test_neq plist a_pairs
(* judge_neq [Eq(Var"x",LVar"x_1");Eq(LVar"x_1",LVar"x_2");Eq(LVar"x_2",LVar"x_3");Eq(Var"y",LVar"y_1");Eq(LVar"y_1",LVar"y_2");Eq(LVar"x_3",LVar"y_2")] (Var"x") (Var"y");; *)
(* The lines below are deprecated *)
(* Here I decreased its efficiency to find inconsistency: the test case below will be true *)
(* And we can use this result to check inconsistency *)
(* judge_neq [Eq(Var"x",Var"y");Neq(Var"x",Var"y")] (Var"x") (Var"y");; *)
(* The lines above are deprecated *)


(******)
(* merge_heap does a very simple merging over two heaps. It's once used in exec Assume and now used in many places. *)
(* It first merges two pure lists into one, and based on that pure list to merge the two sep lists. *)

(* merge_pure merges two pure lists into one, removing any duplicates *)
let rec merge_pure pl_1 pl_2 =
  match pl_1 with
    | [] -> pl_2
    | (Eq(e_1,e_2))::ps ->
        if mem e_2 (find_alias e_1 pl_2) then merge_pure ps pl_2
        else (Eq(e_1,e_2))::(merge_pure ps pl_2)
    | (Neq(e_1,e_2))::ps ->
        if judge_neq pl_2 e_1 e_2 then merge_pure ps pl_2
        else (Neq(e_1,e_2))::(merge_pure ps pl_2)
    | PTop::ps -> PTop::(merge_pure ps pl_2)

(* merge_sep merges two sep lists into one, returning STop for any duplicate in both sep lists *)
let rec merge_sep plist sl_1 sl_2 =
  match sl_1 with
    | [] -> sl_2
    | (Lseg(e_1,e_2))::ss ->
        let sp = find_aliased_head e_1 plist sl_2 in
          if sp = Emp then (Lseg(e_1,e_2))::(merge_sep plist ss sl_2)
          else STop::(merge_sep plist ss sl_2)
    | (Point(e_1,e_2))::ss ->
        let sp = find_aliased_head e_1 plist sl_2 in
          if sp = Emp then (Point(e_1,e_2))::(merge_sep plist ss sl_2)
          else STop::(merge_sep plist ss sl_2)

let merge_heap (SH(pl_1,sl_1)) (SH(pl_2,sl_2)) =
  let plist = merge_pure pl_1 pl_2 in SH(plist, merge_sep plist sl_1 sl_2)

(* merge_heap (SH([Eq(Var"x",LVar"x_1");Eq(Var"y",LVar"y_1");Eq(LVar"y_1",LVar"y_2")], [Lseg(LVar"x_1",Var"y");Point(LVar"y_1",Nil)]))
              (SH ([Eq(LVar"x_2",LVar"x_1");Eq(Var"y",LVar"y_1");Eq(Var"z",Nil)], [Point(LVar"y_1",Nil)]));; *)
