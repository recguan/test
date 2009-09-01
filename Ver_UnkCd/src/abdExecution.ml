open Execution
open Type
open Utils

(* Abductive Execution *)
(* Note the e in the atom commands must be program variables (Var) *)
(* Also we only support one level of dereference over direct variables [x] *)
let abd_exec atom (hp_1, hp_2) =
  match (atom, hp_1) with
    | (_, Top) -> (Top, Top)
    | (Skip, hp_1) -> (hp_1, hp_2)
    | (Assume (SH (pl_1, sl_1)), SH (pl_2, sl_2)) -> ((merge_heap (SH(pl_1,sl_1)) (SH(pl_2,sl_2))), hp_2)
    | (Assert (SH (pl_1, sl_1)), SH (pl_2, sl_2)) -> print_string "(";
        map print_string (map print_pure pl_2); print_endline ";;"; print_newline;
        map print_string (map print_sep sl_2); print_endline ";;"; print_newline;
        map print_string (map print_pure (pure_part hp_2)); print_endline ";;"; print_newline;
        map print_string (map print_sep (sep_part hp_2)); print_string ")"; print_endline ";;"; print_newline;
        (SH (pl_2, sl_2), hp_2) (* Later we need entailment checking here *)
    | (Disp e, SH (plist, slist)) ->
        let sp = find_aliased_head e plist slist in
          if sp <> Emp then
            (SH (plist, elim_lst_ele slist sp), hp_2)
          else (Top, Top) (* Shouldn't happen *)
    | (New (e_1, e_2), SH (plist, slist)) ->
        let sp = find_aliased_head e_1 plist slist in
          if sp = Emp then
            let flvar = fresh_logical e_1 in
              (SH (map (psub flvar e_1) plist, (Point(e_1, esub flvar e_1 e_2))::(map (ssub flvar e_1) slist)), subst flvar e_1 hp_2)
          else (Top, Top) (* Shouldn't happen *)
    | (Assign (Var v, Ref e), SH (plist, slist)) -> (* x:=[E] *)
        let sp = find_aliased_head e plist slist in
          if sp = Emp then (Top, Top) (* Shouldn't happen *)
          else begin
            match sp with Point(e_1, e_2) -> (* cannot be Lseg here *)
              let flvar = fresh_logical (Var v) in
                (SH ((Eq(Var v, esub flvar (Var v) e_2))::(map (psub flvar (Var v)) plist), (map (ssub flvar (Var v)) slist)), subst flvar e_1 hp_2)
          end
    | (Assign (Var v, e), SH (plist, slist)) -> (* x:=E *)
        let flvar = fresh_logical (Var v) in
          (SH ((Eq(Var v, esub flvar (Var v) e))::(map (psub flvar (Var v)) plist), (map (ssub flvar (Var v)) slist)), subst flvar (Var v) hp_2)
    | (Assign (Ref (Var v), e), SH (plist, slist)) -> (* [E]:=G *)
        let sp = find_aliased_head (Var v) plist slist in
          if sp = Emp then (Top, Top) (* Shouldn't happen *)
          else match sp with Point(e_1, e_2) -> (* cannot be Lseg here *)
            (SH (plist, Point(Var v, e)::(elim_lst_ele slist sp)), hp_2)
