open AbdAbstraction
open AbdExecution
open AbdRearrangement
open EntAbd
open List
open Semantic
open Type
open Utils

(* Abductive filter TODO: perhaps add SVar into hp_2 *)
let rec abd_filt b h_pairs =
  match (b, h_pairs) with
    | (b, []) -> []
    | (Eq(e_1,e_2), (SH(plist,slist),hp_2)::hs) ->
        if mem e_1 (find_alias e_2 plist) then ((SH(plist,slist)),hp_2)::(abd_filt b hs)
        else if judge_neq plist e_1 e_2 then abd_filt b hs
        else (SH(Eq(e_1,e_2)::plist,slist),hp_2)::(abd_filt b hs)
    | (Neq(e_1,e_2), (SH(plist,slist),hp_2)::hs) ->
        if mem e_1 (find_alias e_2 plist) then abd_filt b hs
        else if judge_neq plist e_1 e_2 then ((SH(plist,slist)),hp_2)::(abd_filt b hs)
        else (SH(Neq(e_1,e_2)::plist,slist),hp_2)::(abd_filt b hs)

(******)
(* abd_subst_list substs the old version of each var in elist with fresh lvar (heap pair) *)
let rec abd_subst_list elist (hp_1, hp_2) =
  match elist with
    | [] -> (hp_1, hp_2)
    | (Var v)::es -> let flvar = fresh_logical (Var v) in
        abd_subst_list es (subst flvar (Var ("old" ^ v)) hp_1, subst flvar (Var ("old" ^ v)) hp_2)
    | _::es -> abd_subst_list es (hp_1, hp_2)

(******)
(* Semantics for atom instructions *)
let abd_semantic_atom at h_pairs =
  match at with
    | Assign (Var v, Ref e) -> nub (map abd_abs (map (abd_exec at) (nub (flatten (map (abd_rearr e) h_pairs)))))
    | Assign (Ref (Var v), e) -> nub (map abd_abs (map (abd_exec at) (nub (flatten (map (abd_rearr (Var v)) h_pairs)))))
    | Disp e -> nub (map abd_abs (map (abd_exec at) (nub (flatten (map (abd_rearr e) h_pairs)))))
    | other_at -> nub (map abd_abs (map (abd_exec at) h_pairs))

(* Semantics for function call *)
let abd_semantic_func (Fun (name, xs, ys, pre, post)) (hp_1, hp_2) =
  let (frm, abd) = ent_abd hp_1 pre in
    let flvs = map fresh_logical ys in
      let f_y_pairs = combine flvs ys in
        (merge_heap (fold_left pair_subst frm f_y_pairs) (fold_left pair_subst post (flvar_for_old_pairs f_y_pairs)), (fold_left pair_subst (merge_heap abd hp_2) f_y_pairs))

let rec abd_semantic prog h_pairs =
  match prog with
    | Atom at -> abd_semantic_atom at h_pairs
    | Fun (name, xs, ys, pre, post) -> map (abd_semantic_func (Fun (name, xs, ys, pre, post))) h_pairs
    | Seq [] -> h_pairs
    | Seq (sq::sqs) -> abd_semantic (Seq sqs) (abd_semantic sq h_pairs)
    | If (Eq(e_1,e_2), prog_1, prog_2) -> (abd_semantic prog_1 (abd_filt (Eq(e_1,e_2)) h_pairs)) @ (abd_semantic prog_2 (abd_filt (Neq(e_1,e_2)) h_pairs))
    | If (Neq(e_1,e_2), prog_1, prog_2) -> (abd_semantic prog_1 (abd_filt (Neq(e_1,e_2)) h_pairs)) @ (abd_semantic prog_2 (abd_filt (Eq(e_1,e_2)) h_pairs))
    | _ -> [(Top,Top)]
