open List
open Rearrangement
open Type
open Utils

let add_heap_with_point hp tail head =
  match hp with
    | SH(plist, slist) -> SH(plist, (Point(head,tail))::slist)
    | Top -> Top

let abd_rearr e (hp_1, hp_2) =
  let hps_1 = rearr e hp_1 in
  let is_not_top h = h <> Top in
    let hps_sub_top = filter is_not_top hps_1 in
      let states = make_pair hps_sub_top [hp_2] in
        if length hps_sub_top = length hps_1 then states
        else (* There is TOP in hps_1 *)
          let salist = svars_in_explist (find_alias e (pure_part hp_1)) in
            if salist = [] then (Top,Top)::states
            else
              let sp = find_aliased_head e (pure_part hp_2) (sep_part hp_2) in
                match sp with
                  | Emp -> let flvar = fresh_logical e in
                      make_pair [ (SH(pure_part hp_1, (Point(e, flvar))::(sep_part hp_1))) ] (map (add_heap_with_point hp_2 flvar) salist)
                  | _ -> (Top,Top)::states
