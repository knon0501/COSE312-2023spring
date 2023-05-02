open Regex 

exception Not_implemented

let get_final : Nfa.t-> Nfa.state
= fun t -> let fins=(Nfa.get_final_states t) in
                (BatSet.choose fins);;
let rec regex2nfa : Regex.t -> Nfa.t 
=fun t -> match t with
  | Empty -> let nfa=Nfa.create_new_nfa() in
            let (x,nfa)=(Nfa.create_state nfa) in
            (Nfa.add_final_state nfa x) 
  | Epsilon -> let nfa=Nfa.create_new_nfa() in
              let (x,nfa)=(Nfa.create_state nfa) in
              let nfa=(Nfa.add_final_state nfa x) in
              let init=(Nfa.get_initial_state nfa) in 
              (Nfa.add_epsilon_edge nfa (init,x))
  | Alpha(c) -> let nfa=Nfa.create_new_nfa() in
              let (x,nfa)=(Nfa.create_state nfa) in
              let nfa=(Nfa.add_final_state nfa x) in
              let init=(Nfa.get_initial_state nfa) in 
              (Nfa.add_edge nfa (init,c,x))
  | OR(r1,r2) -> let n1=(regex2nfa r1) in
                 let n2=(regex2nfa r2) in
                 let n3=Nfa.create_new_nfa() in
                let (fin,n3)=(Nfa.create_state n3) in
                let n3=(Nfa.add_final_state n3 fin) in
                let init=(Nfa.get_initial_state n3) in
                let n3=(Nfa.add_states n3 (Nfa.get_states n1)) in
                let n3=(Nfa.add_states n3 (Nfa.get_states n2)) in
                let n3=(Nfa.add_edges n3 (Nfa.get_edges n1)) in
                let n3=(Nfa.add_edges n3 (Nfa.get_edges n2)) in
                let n3=(Nfa.add_epsilon_edge n3 (init, (Nfa.get_initial_state n1))) in
                let n3=(Nfa.add_epsilon_edge n3 (init, (Nfa.get_initial_state n2))) in
                let n1_f = get_final(n1) in
                let n2_f = get_final(n2) in
                let n3=(Nfa.add_epsilon_edge n3 (n1_f, fin)) in  
                let n3=(Nfa.add_epsilon_edge n3 (n2_f, fin)) in  n3
  | CONCAT(r1,r2) -> let n1=(regex2nfa r1) in
                      let n2=(regex2nfa r2) in
                      let n3=Nfa.create_new_nfa() in
                    let init=(Nfa.get_initial_state n3) in
                    let n3=(Nfa.add_states n3 (Nfa.get_states n1)) in
                    let n3=(Nfa.add_states n3 (Nfa.get_states n2)) in
                    let n3=(Nfa.add_edges n3 (Nfa.get_edges n1)) in
                    let n3=(Nfa.add_edges n3 (Nfa.get_edges n2)) in
                    let n3=(Nfa.add_epsilon_edge n3 (init, (Nfa.get_initial_state n1))) in
                    let n3=(Nfa.add_epsilon_edge n3 (get_final n1, (Nfa.get_initial_state n2))) in
                    let n3=(Nfa.add_final_state n3 (get_final n2)) in n3
  | STAR(r) ->let n1=(regex2nfa r) in
              let n2=Nfa.create_new_nfa() in
              let (x,n2)=Nfa.create_state(n2) in
              let n2=(Nfa.add_final_state n2 x) in
              let n2=(Nfa.add_states n2 (Nfa.get_states n1)) in
              let n2=(Nfa.add_edges n2 (Nfa.get_edges n1)) in
              let n2=(Nfa.add_epsilon_edge n2 (Nfa.get_initial_state n2,Nfa.get_initial_state n1)) in
              let n2=(Nfa.add_epsilon_edge n2 (get_final n1,get_final n2)) in
              let n2=(Nfa.add_epsilon_edge n2 (Nfa.get_initial_state n2,get_final n2)) in 
              let n2=(Nfa.add_epsilon_edge n2 (get_final n1,Nfa.get_initial_state n1)) in n2;;

let is_final: Dfa.state -> Nfa.t-> bool
= fun state nfa-> BatSet.fold (fun x y -> (Nfa.is_final_state nfa x) || y) state false;;


let rec epsclosure: Nfa.t -> Nfa.state BatSet.t-> Nfa.state BatSet.t->Dfa.state
= fun nfa s states -> if (BatSet.is_empty states) then s else
                      let t= (BatSet.fold
                      (fun x y -> (BatSet.union (Nfa.get_next_state_epsilon nfa x) y ))
                      states BatSet.empty
                      ) in (epsclosure nfa (BatSet.union s t) (BatSet.diff t s));;

let dfa_next: Nfa.t->Dfa.state->alphabet->Dfa.state
= fun nfa state c  -> (BatSet.fold
                      (fun x y -> (BatSet.union (Nfa.get_next_state nfa x c) y))
                        state BatSet.empty
                      );;

let rec nfa3dfa : (Dfa.state BatSet.t)->(Dfa.state list)->(Nfa.t)->(Dfa.t)->(Dfa.t) 
= fun d w  nfa dfa -> match w with 
                      | hd::tl -> let astate= (dfa_next nfa hd A) in
                        let astate = epsclosure nfa astate astate in
                        let bstate = (dfa_next nfa hd B) in
                        let bstate = epsclosure nfa bstate bstate in
                        let w = (if (BatSet.mem astate d) then tl else tl@[astate]) in
                        let w = (if (BatSet.mem bstate d) then w else w@[bstate]) in
                        let d=(BatSet.add astate (BatSet.add bstate d)) in
                        let dfa=(Dfa.add_state dfa astate) in
                        let dfa=(Dfa.add_state dfa bstate) in
                        let dfa=(Dfa.add_edge dfa (hd,A,astate)) in
                        let dfa=(Dfa.add_edge dfa (hd,B,bstate)) in
                        let dfa=(if is_final astate nfa then (Dfa.add_final_state dfa astate) else dfa) in
                        let dfa=(if is_final bstate nfa then (Dfa.add_final_state dfa bstate) else dfa) in
                        (nfa3dfa d w nfa dfa )
                      |  _->dfa;;

let nfa2dfa : Nfa.t -> Dfa.t
=fun t -> let s = (Nfa.get_initial_state t) in
          let initset = (BatSet.singleton s) in
          let _s= (epsclosure t initset initset ) in
          let dfa = (Dfa.create_new_dfa _s) in
          let dfa = if (is_final _s t) then Dfa.add_final_state dfa _s  else dfa in
          let w= [_s] in (nfa3dfa (BatSet.singleton _s) w t dfa);;

          (* Do not modify this function *)
let regex2dfa : Regex.t -> Dfa.t
=fun regex -> 
  let nfa = regex2nfa regex in
  let dfa = nfa2dfa nfa in
    dfa;;

let rec run_dfa2 : Dfa.t -> Dfa.state -> alphabet list -> bool
= fun dfa state lst -> match lst with
                    | hd::tl -> run_dfa2 dfa (Dfa.get_next_state dfa state hd) tl;
                    | _ -> (Dfa.is_final_state dfa state);;

let run_dfa : Dfa.t -> alphabet list -> bool
=fun dfa lst -> run_dfa2 dfa (Dfa.get_initial_state dfa) lst;;