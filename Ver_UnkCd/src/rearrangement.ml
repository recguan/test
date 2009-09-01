open List
open Type
open Utils

(* Rearrangement *)

(* extract_list_before extracts everything in a splist before sp into a new list *)
(* The sp should be sure to exist in splist *)
(* extract_list_before (Lseg(Var"x",Nil)) [(Lseg(Var"y",Nil));(Lseg(Var"x",Nil))];; *)
let rec extract_list_before sp splist =
  match splist with
    | [] -> []
    | s::ss -> if sp = s then [] else s::(extract_list_before sp ss)

(* extract_list_after extracts everything in a splist after sp into a new list *)
(* The sp should be sure to exist in splist *)
(* extract_list_after (Lseg(Var"x",Nil)) [(Lseg(Var"y",Nil));(Lseg(Var"x",Nil))];; *)
let rec extract_list_after sp splist =
  match splist with
    | [] -> []
    | s::ss -> if sp = s then ss else extract_list_after sp ss

(* rearrange takes a var e, a sep constr sp (with the head aliasing to e), the list before sp, and a seplist to rearrange the sp in seplist *)
(* The sp, list_before_sp should correspond to splist by other functions (find_head_from_list, extract_list_before) *)
(* rearrange (Var"x") (Lseg(Var"x",Nil)) [(Lseg(Var"y",Nil))] [(Lseg(Var"y",Nil));(Lseg(Var"x",Nil))];; *)
let rec rearrange e sp list_before_sp splist =
    match (sp, splist) with
      | (Point (e_1, e_2), []) -> [list_before_sp]
      | (Point (e_1, e_2), (Point (e_3, e_4))::ss) ->
          if e_1 = e_3 then [list_before_sp @ ((Point (e, e_2))::ss)]
                       else rearrange e sp list_before_sp ss
      | (Point (e_1, e_2), s::ss) -> rearrange e sp list_before_sp ss
      | (Lseg (e_1, e_2), []) -> [[]]
      | (Lseg (e_1, e_2), (Lseg (e_3, e_4))::ss) ->
          if e_1 = e_3 then
            let flvar = fresh_logical e in
              [list_before_sp @ ((Point(e,e_2))::ss);
               list_before_sp @ ((Point(e,flvar))::(Lseg(flvar,e_2))::ss)]
          else rearrange e sp list_before_sp ss
      | (Lseg (e_1, e_2), s::ss) -> rearrange e sp list_before_sp ss
      | (sp, splist) -> [[STop]]

(* rearr does the real rearrangement *)
let rearr e hp =
  match hp with
    | SH (plist, splist) ->
        let sp = find_aliased_head e plist splist in
          if sp <> Emp then
            let list_before_sp = extract_list_before sp splist in
            let new_splist_list = rearrange e sp list_before_sp splist in
              if new_splist_list <> [[STop]] then make_heap_pair [plist] new_splist_list
              else [Top]
          else [Top] 
    | _ -> [Top]
(* rearr (Var "x") (SH([Eq(Var"x",LVar"x_1"); Eq(LVar"x_1",LVar"x_2"); Neq(LVar"x_1",LVar"x_3"); Neq(LVar"x_1",Var"y"); Eq(LVar"x_4",LVar"x_1"); Eq(LVar"x_4",LVar"x_5")], [Lseg(Var"x",Nil); Point(Var"y",Nil); Lseg(LVar"x_3",Var"y")]));; *)
