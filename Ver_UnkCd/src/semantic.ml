open Abstraction
open EntAbd
open Execution
open List
open Rearrangement
open Type
open Utils

(* Main function for filter *)
let rec filt b hps =
  match (b, hps) with
    | (b, []) -> []
    | (Eq(e_1,e_2), (SH(plist,slist))::hs) ->
        if mem e_1 (find_alias e_2 plist) then (SH(plist,slist))::(filt b hs)
        else if judge_neq plist e_1 e_2 then filt b hs
        else (SH(Eq(e_1,e_2)::plist,slist))::(filt b hs)
    | (Neq(e_1,e_2), (SH(plist,slist))::hs) ->
        if mem e_1 (find_alias e_2 plist) then filt b hs
        else if judge_neq plist e_1 e_2 then (SH(plist,slist))::(filt b hs)
        else (SH(Neq(e_1,e_2)::plist,slist))::(filt b hs)
(* filt (Eq(Var"x",Var"y")) [SH([Eq(Var"x",LVar"x_1");Eq(LVar"x_1",LVar"x_2");Eq(LVar"x_2",LVar"x_3");Eq(Var"y",LVar"y_1");Eq(LVar"y_1",LVar"y_2");Eq(LVar"x_3",LVar"y_2")],[]);SH([Eq(Var"x",LVar"x_1");Eq(LVar"x_1",LVar"x_2");Eq(LVar"x_2",LVar"x_3");Eq(Var"y",LVar"y_1");Eq(LVar"y_1",LVar"y_2");Neq(LVar"x_3",LVar"y_2")],[])];; *)

(******)
(* gen_flvar_old_pairs generates pairs of (flvar, old) for a list of substitutions *)
let rec gen_flvar_old_pairs elist =
  match elist with
    | [] -> []
    | (Var v)::es -> (fresh_logical (Var v), Var ("old" ^ v))::gen_flvar_old_pairs es
    | _::es -> gen_flvar_old_pairs es

(******)
(* Semantics for atom instructions *)
let semantic_atom at hps =
  match at with
    | Assign (Var v, Ref e) -> nub (map abs (map (exec at) (nub (flatten (map (rearr e) hps)))))
    | Assign (Ref (Var v), e) -> nub (map abs (map (exec at) (nub (flatten (map (rearr (Var v)) hps)))))
    | Disp e -> nub (map abs (map (exec at) (nub (flatten (map (rearr e) hps)))))
    | other_at -> nub (map abs (map (exec at) hps))

let semantic_func (Fun (name, xs, ys, pre, post)) hp =
  let (frm, abd) = ent_abd hp pre in
    let flvs = map fresh_logical ys in
      let f_y_pairs = combine flvs ys in
        if sep_part (abd) = [] then (merge_heap (fold_left pair_subst frm f_y_pairs) (fold_left pair_subst post (flvar_for_old_pairs f_y_pairs))) else Top
(* TODO: Or maybe it should be (sep_part abd) = [] / abd = SH([], [])? Of course not simply that but still need further consideration. *)

let rec semantic prog hps =
  match prog with
    | Atom at -> semantic_atom at hps
    (* Note that pre and post should be in terms of actual paras and post should have ys and oldys *)
    | Fun (name, xs, ys, pre, post) -> map (semantic_func (Fun (name, xs, ys, pre, post))) hps
    | Seq [] -> hps
    | Seq (sq::sqs) -> semantic (Seq sqs) (semantic sq hps)
    | If (Eq(e_1,e_2), prog_1, prog_2) -> (semantic prog_1 (filt (Eq(e_1,e_2)) hps)) @ (semantic prog_2 (filt (Neq(e_1,e_2)) hps))
    | If (Neq(e_1,e_2), prog_1, prog_2) -> (semantic prog_1 (filt (Neq(e_1,e_2)) hps)) @ (semantic prog_2 (filt (Eq(e_1,e_2)) hps))
    | _ -> [Top]

(*
let prog = Seq [ Atom(Assign(Var"w", Ref(Var"x")));
                 If(Eq(Var"w",Nil), Atom(Skip), Seq [ Atom(Assign(Var"x",Var"w"));
                    Fun ("fT",[],[Var"x"], SH([Neq(Var"x",Nil)],[Lseg(Var"x",Nil)]),
                         SH([],[Lseg(Var"oldx",Var"x");Point(Var"x",Nil)]))]) ] in
semantic prog [SH([Neq(Var"x",Nil)],[Lseg(Var"x",Nil)])];;

semantic (Fun ("fT",[],[Var"x"], SH([Neq(Var"x",Nil)],[Lseg(Var"x",Nil)]), 
 SH([],[Lseg(Var"oldx",Var"x");Point(Var"x",Nil)])))
[SH ([Eq (Var "w", Nil); Neq (Var "x", Nil)], [Point (Var "x", Nil)]);
 SH ([Eq (Var "w", Nil); Neq (Var "x", Nil)],
  [Point (Var "x", Var "w"); Lseg (Var "w", Nil)]);
 SH
  ([Eq (Var "x", Var "w"); Neq (Var "w", Nil); Neq (LVar "x_10008", Nil)],
  [Point (LVar "x_10008", Var "w"); Lseg
 (Var "w", Nil)])];;
*)