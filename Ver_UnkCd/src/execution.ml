open List
open Print
open Type
open Utils

(* Execution *)
(* Note the e in the atom commands must be program variables (Var) *)
(* Also we only support one level of dereference over direct variables [x] *)
let exec atom hp =
  match (atom, hp) with
    | (_, Top) -> Top
    | (Skip, hp) -> hp
    | (Assume (SH (pl_1, sl_1)), SH (pl_2, sl_2)) -> merge_heap (SH(pl_1,sl_1)) (SH(pl_2,sl_2))
    | (Assert (SH (pl_1, sl_1)), SH (pl_2, sl_2)) ->
        map print_string (map print_pure pl_2); print_endline ";;"; print_newline;
        map print_string (map print_sep sl_2); print_endline ";;"; print_newline;
        SH (pl_2, sl_2) (* Later we need entailment checking here *)
    | (Disp e, SH (plist, slist)) ->
        let sp = find_aliased_head e plist slist in
          if sp <> Emp then
            SH (plist, elim_lst_ele slist sp)
          else Top (* Shouldn't happen *)
    | (New (e_1, e_2), SH (plist, slist)) ->
        let sp = find_aliased_head e_1 plist slist in
          if sp = Emp then
            let flvar = fresh_logical e_1 in
              SH (map (psub flvar e_1) plist, (Point(e_1, esub flvar e_1 e_2))::(map (ssub flvar e_1) slist))
          else Top (* Shouldn't happen *)
    | (Assign (Var v, Ref e), SH (plist, slist)) -> (* x:=[E] *)
        let sp = find_aliased_head e plist slist in
          if sp = Emp then Top (* Shouldn't happen *)
          else begin
            match sp with Point(e_1, e_2) -> (* cannot be Lseg here *)
              let flvar = fresh_logical (Var v) in
                SH ((Eq(Var v, esub flvar (Var v) e_2))::(map (psub flvar (Var v)) plist), (map (ssub flvar (Var v)) slist))
          end
    | (Assign (Var v, e), SH (plist, slist)) -> (* x:=E *)
        let flvar = fresh_logical (Var v) in
          SH ((Eq(Var v, esub flvar (Var v) e))::(map (psub flvar (Var v)) plist), (map (ssub flvar (Var v)) slist))
    | (Assign (Ref (Var v), e), SH (plist, slist)) -> (* [E]:=G *)
        let sp = find_aliased_head (Var v) plist slist in
          if sp = Emp then Top (* Shouldn't happen *)
          else match sp with Point(e_1, e_2) -> (* cannot be Lseg here *)
            SH (plist, Point(Var v, e)::(elim_lst_ele slist sp))
(* exec Skip (SH ([Eq(Var"x",LVar"x_1");Eq(LVar"x_2",LVar"x_1");Eq(Var"y",LVar"y_1");Eq(LVar"y_1",LVar"y_2");Eq(Var"z",Nil)], [Lseg(LVar"x_1",Var"y");Point(LVar"y_1",Nil)]));; *)
(* exec (Disp(Var"y")) (SH ([Eq(Var"x",LVar"x_1");Eq(LVar"x_2",LVar"x_1");Eq(Var"y",LVar"y_1");Eq(LVar"y_1",LVar"y_2");Eq(Var"z",Nil)], [Lseg(LVar"x_1",Var"y");Point(LVar"y_1",Nil)]));; *)
(* exec (New(Var"z",Nil)) (SH ([Eq(Var"x",LVar"x_1");Eq(LVar"x_2",LVar"x_1");Eq(Var"y",LVar"y_1");Eq(LVar"y_1",LVar"y_2");Eq(Var"z",Nil)], [Lseg(LVar"x_1",Var"y");Point(LVar"y_1",Nil)]));; *)
(* exec (Assign(Var"x",Ref(Var"y"))) (SH ([Eq(Var"x",LVar"x_1");Eq(LVar"x_2",LVar"x_1");Eq(Var"y",LVar"y_1");Eq(LVar"y_1",LVar"y_2");Eq(Var"z",Nil)], [Lseg(LVar"x_1",Var"y");Point(LVar"y_1",Nil)]));; *)
(* exec (Assign(Var"x",Var"z")) (SH ([Eq(Var"x",LVar"x_1");Eq(LVar"x_2",LVar"x_1");Eq(Var"y",LVar"y_1");Eq(LVar"y_1",LVar"y_2");Eq(Var"z",Nil)], [Lseg(LVar"x_1",Var"y");Point(LVar"y_1",Nil)]));; *)
(* exec (Assign(Ref(Var"x"),Var"y")) (hd (tl(rearr (Var"x") (SH ([Eq(Var"x",LVar"x_1");Eq(LVar"x_2",LVar"x_1");Eq(Var"y",LVar"y_1");Eq(LVar"y_1",LVar"y_2");Eq(Var"z",Nil)], [Lseg(LVar"x_1",Var"y");Point(LVar"y_1",Nil)])))));; *)
