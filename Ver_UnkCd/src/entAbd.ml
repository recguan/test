open Type
open Utils
open List

(******)
(* Entailment and abduction *)

let rec ent_abd_head (SH(pl_1, sl_1), SH(pl_2, sl_2)) =
  match sl_2 with
    | [] -> ((SH(pl_1, sl_1)), (SH(pl_2, [])))
    | Emp::ss_2 -> ent_abd_head (SH(pl_1, sl_1), SH(pl_2, ss_2))
    | Junk::ss_2 ->
        let ((SH(r_pl_1, r_sl_1)), (SH(r_pl_2, r_sl_2))) = ent_abd_head (SH(pl_1, sl_1), SH(pl_2, ss_2)) in
          ((SH(r_pl_1, r_sl_1)), (SH(r_pl_2, Junk::r_sl_2)))
    | (Point(e_1,e_2))::ss_2 -> (* missing, pnt-match and lseg-left *)
        let s_1 = find_aliased_head e_1 pl_1 sl_1 in begin
            match s_1 with
              | Emp -> let (SH(r_pl_1,r_sl_1), SH(r_pl_2,r_sl_2)) = ent_abd_head (SH(pl_1, sl_1), SH(pl_2, ss_2)) in
                  (SH(r_pl_1,r_sl_1), SH(r_pl_2,(Point(e_1,e_2))::r_sl_2))
              | Point(e_3,e_4) -> ent_abd_head (SH(pl_1, elim_lst_ele sl_1 s_1), SH((Eq(e_2,e_4))::pl_2,ss_2))
              | Lseg(e_3,e_4) -> ent_abd_head (SH(pl_1,(Lseg(e_2,e_4))::(elim_lst_ele sl_1 s_1)), SH((Neq(e_3,e_4))::pl_2,sl_2))
          end
    | (Lseg(e_1,e_2))::ss_2 -> (* missing, lseg-right *)
        let s_1 = find_aliased_head e_1 pl_1 sl_1 in begin
            match s_1 with
              | Emp -> let (SH(r_pl_1,r_sl_1), SH(r_pl_2,r_sl_2)) = ent_abd_head (SH(pl_1, sl_1), SH(pl_2, ss_2)) in
                  (SH(r_pl_1,r_sl_1), SH(r_pl_2,(Lseg(e_1,e_2))::r_sl_2))
              | Point(e_3,e_4) -> ent_abd_head (SH(pl_1, elim_lst_ele sl_1 s_1), SH(pl_2,(Lseg(e_4,e_2))::ss_2))
              | Lseg(e_3,e_4) -> ent_abd_head (SH(pl_1, elim_lst_ele sl_1 s_1), SH(pl_2,(Lseg(e_4,e_2))::ss_2))
          end
(* ent_abd_head (SH([],[Lseg(Var"x",Var"z");Point(SVar"a",SVar"b")]), SH([],[Lseg(Var"x",Var"y");Point(SVar"c",SVar"b")])) ;; *)

let rec ent_abd_tail (SH(pl_1, sl_1), SH(pl_2, sl_2)) =
  match sl_2 with
    | [] -> ((SH(pl_1, sl_1)), (SH(pl_2, [])))
    | Emp::ss_2 -> ent_abd_tail (SH(pl_1, sl_1), SH(pl_2, ss_2))
    | Junk::ss_2 ->
        let ((SH(r_pl_1, r_sl_1)), (SH(r_pl_2, r_sl_2))) = ent_abd_tail (SH(pl_1, sl_1), SH(pl_2, ss_2)) in
          ((SH(r_pl_1, r_sl_1)), (SH(r_pl_2, Junk::r_sl_2)))
    | (Point(e_1,e_2))::ss_2 -> (* missing, pnt-match and lseg-left *)
        if mem Nil (find_alias e_2 pl_2) then
          let (SH(r_pl_1,r_sl_1), SH(r_pl_2,r_sl_2)) = ent_abd_tail (SH(pl_1, sl_1), SH(pl_2, ss_2)) in
            (SH(r_pl_1,r_sl_1), SH(r_pl_2,(Point(e_1,e_2))::r_sl_2))
        else let s_1 = find_aliased_tail e_2 pl_1 sl_1 in begin
            match s_1 with
              | Emp -> let (SH(r_pl_1,r_sl_1), SH(r_pl_2,r_sl_2)) = ent_abd_tail (SH(pl_1, sl_1), SH(pl_2, ss_2)) in
                  (SH(r_pl_1,r_sl_1), SH(r_pl_2,(Point(e_1,e_2))::r_sl_2))
              | Point(e_3,e_4) -> ent_abd_tail (SH(pl_1, elim_lst_ele sl_1 s_1), SH((Eq(e_1,e_3))::pl_2,ss_2))
              | Lseg(e_3,e_4) -> ent_abd_tail (SH(pl_1,(Lseg(e_3,e_1))::(elim_lst_ele sl_1 s_1)), SH((Neq(e_3,e_4))::pl_2,sl_2))
          end
    | (Lseg(e_1,e_2))::ss_2 -> (* missing, lseg-right *)
        if mem Nil (find_alias e_2 pl_2) then
          let (SH(r_pl_1,r_sl_1), SH(r_pl_2,r_sl_2)) = ent_abd_tail (SH(pl_1, sl_1), SH(pl_2, ss_2)) in
            (SH(r_pl_1,r_sl_1), SH(r_pl_2,(Lseg(e_1,e_2))::r_sl_2))
        else let s_1 = find_aliased_tail e_2 pl_1 sl_1 in begin
            match s_1 with
              | Emp -> let (SH(r_pl_1,r_sl_1), SH(r_pl_2,r_sl_2)) = ent_abd_tail (SH(pl_1, sl_1), SH(pl_2, ss_2)) in
                  (SH(r_pl_1,r_sl_1), SH(r_pl_2,(Lseg(e_1,e_2))::r_sl_2))
              | Point(e_3,e_4) -> ent_abd_tail (SH(pl_1, elim_lst_ele sl_1 s_1), SH(pl_2,(Lseg(e_1,e_3))::ss_2))
              | Lseg(e_3,e_4) -> ent_abd_tail (SH(pl_1, elim_lst_ele sl_1 s_1), SH(pl_2,(Lseg(e_1,e_3))::ss_2))
          end
(* ent_abd_tail (SH([],[Lseg(Var"x",Var"z");Point(SVar"a",SVar"b")]), SH([],[Lseg(Var"x",Var"y");Point(SVar"c",SVar"b")])) ;; *)
(* let (hp_1, hp_2) = ent_abd_head (SH([],[Lseg(Var"x",Var"z");Point(SVar"a",SVar"b")]), SH([],[Lseg(Var"x",Var"y");Point(SVar"c",SVar"b")])) in ent_abd_tail (hp_1, hp_2) ;; *)

(* Entailment and abduction within pure part *)
let rec ent_abd_pure plist_1 slist_1 plist_2 =
  match plist_2 with
    | [] -> (plist_1, [])
    | (Eq(e_1,e_2))::ps ->
        if mem e_2 (find_alias e_1 plist_1) then ent_abd_pure plist_1 slist_1 ps
        else let (pl_1, pl_2) = ent_abd_pure ((Eq(e_1,e_2))::plist_1) slist_1 ps in
          (pl_1, (Eq(e_1,e_2))::pl_2)
    | (Neq(e_1,Nil))::ps -> let sp = find_aliased_head e_1 plist_1 slist_1 in begin
          match sp with (* e_1 points to sth and cannot be Nil *)
            | Point(e_p, e_q) -> ent_abd_pure plist_1 slist_1 ps
            | _ -> let (pl_1, pl_2) = ent_abd_pure ((Neq(e_1,Nil))::plist_1) slist_1 ps in (pl_1, (Neq(e_1,Nil))::pl_2)
        end
    | (Neq(Nil,e_1))::ps -> ent_abd_pure plist_1 slist_1 ((Neq(e_1,Nil))::ps)
    | (Neq(e_1,e_2))::ps ->
        if judge_neq plist_1 e_1 e_2 then ent_abd_pure plist_1 slist_1 ps
        else let (pl_1, pl_2) = ent_abd_pure ((Neq(e_1,e_2))::plist_1) slist_1 ps in
          (pl_1, (Neq(e_1,e_2))::pl_2)
    | PTop::ps -> ([PTop], [PTop])

let rec check_consist_pure plist g_plist =
  match plist with
    | [] -> true
    | (Neq(e_1,e_2))::ps -> if mem e_1 (find_alias e_2 plist) then false else check_consist_pure ps g_plist
    | PTop::ps -> false
    | _::ps -> check_consist_pure ps g_plist

let rec check_consist_sep plist slist =
  match slist with
    | [] -> true
    | (Lseg(e_1,e_2))::ss -> if find_aliased_head e_1 plist ss = Emp then check_consist_sep plist ss else false
    | (Point(e_1,e_2))::ss -> if find_aliased_head e_1 plist ss = Emp then check_consist_sep plist ss else false
    | STop::ss -> false
    | _::ss -> check_consist_sep plist ss

let check_consist_heap hp =
  match hp with
    | Top -> false
    | SH(plist, slist) -> (check_consist_pure plist plist) && (check_consist_sep plist slist)

let check_consist_heap_pair (hp_1, hp_2) = (check_consist_heap hp_1) && (check_consist_heap hp_2)

let rec heap_clear hp =
  match hp with
    | SH(pl, []) -> SH(pl, [])
    | SH(pl, (Lseg(e_1,e_2))::sl) ->
        if mem e_1 (find_alias e_2 pl) then heap_clear (SH(pl,sl))
        else SH(pl, (Lseg(e_1,e_2))::(sep_part (heap_clear (SH(pl,sl)))))
    | SH(pl, s::sl) -> SH(pl, s::(sep_part (heap_clear (SH(pl,sl)))))
    | Top -> Top

let ent_abd hp_1 hp_2 =
  let (hp_3, hp_4) = ent_abd_tail (ent_abd_head (hp_1, hp_2)) in
    let hp_5 = heap_clear hp_3 in
    let hp_6 = heap_clear hp_4 in
      if (check_consist_heap hp_5) && (check_consist_heap hp_6) then (hp_5, hp_6) else (Top, Top)

(* ent_abd (SH([],[Point(Var"x",Nil);Point(Var"z",Nil)])) (SH([],[Lseg(Var"x",Nil);Lseg(Var"y",Nil)]));; *)
(* ent_abd (SH([],[Point(Var"x",Var"y")])) (SH([],[Point(Var"x",LVar"a");Lseg(LVar"a",Nil)]));; *)
(* ent_abd (SH([],[Point(Var"x",Var"z")])) (SH([],[Lseg(Var"x",Var"z");Lseg(Var"y",Nil)]));; *)
(* ent_abd (SH([],[Point(Var"x",LVar"3")])) (SH([],[Point(Var"y",LVar"3")]));; *)
