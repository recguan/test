open List
open Type
open Utils

(* Abstraction *)

(* Abs Rules *)
(* TODO: test cases needed *)

(* When we have x'=E or E=x' just substitute the x' with E and remove x'=E or E=x' *)
let rec st_1_2 (SH(plist, slist)) =
  match plist with
    | [] -> SH([], slist)
    | (Eq(e, LVar lv))::ps -> st_1_2 (subst e (LVar lv) (SH(ps,slist)))
    | (Eq(LVar lv, e))::ps -> st_1_2 (subst e (LVar lv) (SH(ps,slist)))
    | p::ps -> let hp = (st_1_2 (SH(ps,slist))) in
        match hp with SH(plist,slist) -> SH(p::plist,slist)
(* st_1_2 (SH([Eq(Var"x",LVar"x_1");Eq(LVar"x_2",LVar"x_1");Eq(Var"y",LVar"y_1");Eq(LVar"y_1",LVar"y_2");Eq(Var"z",Nil)], [Lseg(LVar"x_1",Var"y");Point(LVar"y_1",Nil)]));; *)

(* gb_1_slist is called by gb_1 to process slist first (since there's no change to plist), with all lvars in the plist *)
let rec gb_1_slist lvars_plist g_slist slist =
  match slist with
    | [] -> []
    | (Point(LVar lv, e))::ss ->
        let new_g_slist = elim_lst_ele g_slist (Point(LVar lv, e)) in
          if not (mem (LVar lv) (lvars_plist @ (lvars_in [] new_g_slist []))) then Junk::(gb_1_slist lvars_plist new_g_slist ss)
          else (Point(LVar lv, e))::(gb_1_slist lvars_plist g_slist ss)
    | (Lseg(LVar lv, e))::ss ->
        let new_g_slist = elim_lst_ele g_slist (Lseg(LVar lv, e)) in
          if not (mem (LVar lv) (lvars_plist @ (lvars_in [] new_g_slist []))) then Junk::(gb_1_slist lvars_plist new_g_slist ss)
          else (Lseg(LVar lv, e))::(gb_1_slist lvars_plist g_slist ss)
    | s::ss -> s::(gb_1_slist lvars_plist g_slist ss)

let gb_1 (SH(plist, slist)) =
  let lvars_plist = lvars_in plist [] [] in
    SH(plist, gb_1_slist lvars_plist slist slist)
(* gb_1 (SH([Eq(Var"x",LVar"x_1");Eq(Var"y",LVar"y_1");Eq(Var"z",Nil)], [Lseg(LVar"x_2",Var"y");Point(LVar"y_1",Nil)]));; *)

(* gb_2_slist is called by gb_1 to process slist first (since there's no change to plist), with all lvars in the plist *)
let rec gb_2_slist lvars_plist slist =
  match slist with
    | [] -> []
    (* Here is a possible bug: when found Point(x',y'), I just look forward till the end for Point(y',x'); is it necessary to look in the whole slist? *)
    | (Point(LVar x, LVar y))::ss ->
        if (mem (Point(LVar y, LVar x)) ss) && not (mem (LVar x) lvars_plist) && not (mem (LVar y) lvars_plist) then
          let newss = elim_lst_ele ss (Point(LVar y, LVar x)) in
            let lvars_slist = lvars_in [] newss [] in
              if not (mem (LVar x) lvars_slist) && not (mem (LVar y) lvars_slist) then Junk::(gb_2_slist lvars_plist newss)
              else (Point(LVar x, LVar y))::(gb_2_slist lvars_plist ss)
        else if (mem (Lseg(LVar y, LVar x)) ss) && not (mem (LVar x) lvars_plist) && not (mem (LVar y) lvars_plist) then
          let newss = elim_lst_ele ss (Lseg(LVar y, LVar x)) in
            let lvars_slist = lvars_in [] newss [] in
              if not (mem (LVar x) lvars_slist) && not (mem (LVar y) lvars_slist) then Junk::(gb_2_slist lvars_plist newss)
              else (Point(LVar x, LVar y))::(gb_2_slist lvars_plist ss)
        else (Point(LVar x, LVar y))::(gb_2_slist lvars_plist ss)
    | (Lseg(LVar x, LVar y))::ss ->
        if (mem (Lseg(LVar y, LVar x)) ss) && not (mem (LVar x) lvars_plist) && not (mem (LVar y) lvars_plist) then
          let newss = elim_lst_ele ss (Lseg(LVar y, LVar x)) in
            let lvars_slist = lvars_in [] newss [] in
              if not (mem (LVar x) lvars_slist) && not (mem (LVar y) lvars_slist) then Junk::(gb_2_slist lvars_plist newss)
              else (Lseg(LVar x, LVar y))::(gb_2_slist lvars_plist ss)
        else if (mem (Point(LVar y, LVar x)) ss) && not (mem (LVar x) lvars_plist) && not (mem (LVar y) lvars_plist) then
          let newss = elim_lst_ele ss (Point(LVar y, LVar x)) in
            let lvars_slist = lvars_in [] newss [] in
              if not (mem (LVar x) lvars_slist) && not (mem (LVar y) lvars_slist) then Junk::(gb_2_slist lvars_plist newss)
              else (Lseg(LVar x, LVar y))::(gb_2_slist lvars_plist ss)
        else (Lseg(LVar x, LVar y))::(gb_2_slist lvars_plist ss)
    | s::ss -> s::(gb_2_slist lvars_plist ss)

let gb_2 (SH(plist, slist)) =
  SH(plist, gb_2_slist (lvars_in plist [] []) slist)
(* gb_2 (SH([], [Lseg(Var"x",LVar"x_2");Lseg(LVar"x_1",LVar"y_1");Point(LVar"y_1",LVar"x_1");Point(Var"y",LVar"x_2")]));; *)

(* The two rules of abs_1 and _2 are combined in one *)

(* abs_slist_judge_f judges whether f is nil or still the head of another lseg *)
let abs_slist_judge_f plist new_slist e lv lv_1 f =
  let f_alias = find_alias f plist in
    if (mem Nil f_alias) && not (mem (LVar lv) (lvars_in plist new_slist [e; f])) then Lseg(e, Nil)
    else let sp = find_aliased_head f plist new_slist in
      if sp <> Emp then Lseg(e, f)
      else Emp

(* Only the last parameter will be matched; however note the second parameter is not matched but still mutable *)
let rec abs_slist plist g_slist slist =
  match slist with
    | [] -> []
    | (Point(e, LVar lv))::ss ->
        let new_sep = find_head_in_heap (LVar lv) g_slist in
          if new_sep <> Emp then begin
              match new_sep with
                | Point(LVar lv_1, f) ->
                    let new_slist = List.fold_left elim_lst_ele g_slist [Point(e, LVar lv); Point(LVar lv_1, f)] in
                      let res = abs_slist_judge_f plist new_slist e lv lv_1 f in
                        if res = Emp then (Point(e, LVar lv))::(abs_slist plist g_slist ss)
                        else res::(abs_slist plist new_slist (elim_lst_ele ss (Point(LVar lv_1, f))))
                | Lseg(LVar lv_1, f) ->
                    let new_slist = List.fold_left elim_lst_ele g_slist [Point(e, LVar lv); Lseg(LVar lv_1, f)] in
                      let res = abs_slist_judge_f plist new_slist e lv lv_1 f in
                        if res = Emp then (Point(e, LVar lv))::(abs_slist plist g_slist ss)
                        else res::(abs_slist plist new_slist (elim_lst_ele ss (Lseg(LVar lv_1, f))))
            end
          else (Point(e, LVar lv))::(abs_slist plist g_slist ss)
    | (Lseg(e, LVar lv))::ss ->
        let new_sep = find_head_in_heap (LVar lv) g_slist in
          if new_sep <> Emp then begin
              match new_sep with
                | Point(LVar lv_1, f) ->
                    let new_slist = List.fold_left elim_lst_ele g_slist [Lseg(e, LVar lv); Point(LVar lv_1, f)] in
                      let res = abs_slist_judge_f plist new_slist e lv lv_1 f in
                        if res = Emp then (Lseg(e, LVar lv))::(abs_slist plist g_slist ss)
                        else res::(abs_slist plist new_slist (elim_lst_ele ss (Point(LVar lv_1, f))))
                | Lseg(LVar lv_1, f) ->
                    let new_slist = List.fold_left elim_lst_ele g_slist [Lseg(e, LVar lv); Lseg(LVar lv_1, f)] in
                      let res = abs_slist_judge_f plist new_slist e lv lv_1 f in
                        if res = Emp then (Lseg(e, LVar lv))::(abs_slist plist g_slist ss)
                        else res::(abs_slist plist new_slist (elim_lst_ele ss (Lseg(LVar lv_1, f))))
            end
          else (Lseg(e, LVar lv))::(abs_slist plist g_slist ss)
    | s::ss -> s::(abs_slist plist g_slist ss)

let abs_1_2 (SH(plist, slist)) = SH (plist, abs_slist plist slist slist)

(* Overall abs function to perform abstraction over one symbolic heap *)
(* First try all rules one by one, then see whether a fixpoint is reached *)

let rec abs hp =
  match hp with
    | Top -> Top
    | hp -> let new_hp = abs_1_2 (gb_2 (gb_1 (st_1_2 hp))) in
        if hp = new_hp then hp else abs new_hp

(* abs (SH([],[Lseg(Var"x",LVar"x_1");Lseg(Var"y",LVar"x_1");Lseg(LVar"x_1",Nil)]));; *)
(* abs (SH([],[Lseg(Var"x",LVar"x_1");Lseg(LVar"x_1",LVar"y_1");Lseg(LVar"y_1",Nil)]));; *)
(* abs (SH([],[Lseg(Var"x",LVar"x_1");Lseg(LVar"x_1",Var"x")]));; *)
(* abs (SH([],[Lseg(Var"x",LVar"y_1");Lseg(LVar"y_1",LVar"x_1");Lseg(LVar"x_1",Var"x")]));; *)
(* abs (SH([],[Lseg(Var"x",LVar"x_1")]));; *)
(* abs (SH([],[Lseg(LVar"x_1",Var"x")]));; *)
(* abs (SH([],[Lseg(Var"x",LVar"x_1");Lseg(LVar"x_1",Var"y")]));; *)
(* abs (SH([Eq(LVar"y_1",Var"y")],[Lseg(Var"x",LVar"x_1");Point(LVar"x_1",Var"y");Lseg(LVar"y_1",Var"z")]));; *)
