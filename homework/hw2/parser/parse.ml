open Util

type symbol = T of string | N of string | Epsilon | End
type production = symbol * symbol list
type cfg = symbol list * symbol list * symbol * production list

let string_of_symbol s = 
  match s with 
  | T x -> x 
  | N x -> x 
  | Epsilon -> "epsilon"
  | End -> "$"

let string_of_prod (lhs, rhs) = 
    string_of_symbol lhs ^ " -> " ^ 
      string_of_list ~first:"" ~last:"" ~sep:" " string_of_symbol rhs 

module FIRST = struct 
  type t = (symbol, symbol BatSet.t) BatMap.t

  let empty = BatMap.empty 
  
  let find : symbol -> t -> symbol BatSet.t 
  =fun s t -> try BatMap.find s t with _ -> BatSet.empty 
  
  let add : symbol -> symbol -> t -> t 
  =fun s1 s2 t -> BatMap.add s1 (BatSet.add s2 (find s1 t)) t
  
  let add_set : symbol -> symbol BatSet.t -> t -> t 
  =fun s1 ss t -> BatSet.fold (fun s2 -> add s1 s2) ss t

  let tostring : t -> string
  =fun t -> 
    BatMap.foldi (fun s ss str -> 
      str ^ string_of_symbol s ^ " |-> " ^ string_of_set string_of_symbol ss ^ "\n"
    ) t ""
end   

module FOLLOW = struct
  type t = (symbol, symbol BatSet.t) BatMap.t 

  let empty = BatMap.empty 

  let find : symbol -> t -> symbol BatSet.t 
  =fun s t -> try BatMap.find s t with _ -> BatSet.empty 

  let add : symbol -> symbol -> t -> t 
  =fun s1 s2 t -> BatMap.add s1 (BatSet.add s2 (find s1 t)) t

  let add_set : symbol -> symbol BatSet.t -> t -> t 
  =fun s1 ss t -> BatSet.fold (fun s2 -> add s1 s2) ss t

  let tostring : t -> string
  =fun t -> 
    BatMap.foldi (fun s ss str -> 
      str ^ string_of_symbol s ^ " |-> " ^ string_of_set string_of_symbol ss ^ "\n"
    ) t ""
end

module ParsingTable = struct
  type t = (symbol * symbol, (symbol * symbol list) BatSet.t) BatMap.t 

  let empty = BatMap.empty 

  let find (nonterm, term) t = try BatMap.find (nonterm, term) t with _ -> BatSet.empty 

  let add (nonterm, term) prod t = 
    BatMap.add (nonterm, term) (BatSet.add prod (find (nonterm, term) t)) t
    
  let tostring : t -> string 
  =fun t -> 
    BatMap.foldi (fun (nonterm, term) prods str -> 
      str ^ string_of_symbol nonterm ^ ", " ^ string_of_symbol term ^ " |-> " ^
        string_of_set string_of_prod prods ^ "\n"
    ) t ""
    
  let foldi = BatMap.foldi 

  let for_all = BatMap.for_all
end

let rec getp: symbol->production list->symbol list list->symbol list list
= fun s plst ret-> match plst with 
                  | hd::tl -> (match hd with (x,y) -> 
                    if x=s then (getp s tl (ret@[y])) else (getp s tl ret))
                  | _-> ret;;




let rec get_first: symbol ->production list -> FIRST.t -> symbol BatSet.t->symbol BatSet.t*bool
= fun s plst first dup-> if (BatSet.mem s dup) then (BatSet.empty,true) else
                      let dup = (BatSet.add s dup) in
                      let exi= (FIRST.find s first) in
                      if (BatSet.is_empty exi) then
                      (let p = (getp s plst []) in
                        list_fold (fun x (y1,y2) -> 
    
                          (
                            if x=[] then (BatSet.add Epsilon y1,y2)
                            else (
                            let res=(
                              list_fold (fun z (fst,flag,is_leftrec)-> 
                              if flag then 
                                  (
                                  if z = s then (fst,flag,true) 
                                  else ( 
                                    let (fstz,flag2)=(get_first z plst first dup) in
                                    let flag= ((BatSet.mem Epsilon fstz)&&flag) in
                                    let fstz =(BatSet.remove Epsilon fstz) in                                
                                    (BatSet.union fstz fst, flag,is_leftrec || flag2) 
                                  )
                                  )
                              else (fst,flag,is_leftrec)
                                ) x (y1,true,y2) 
                                
                              )
                            in match res with (fst,flag,is_leftrec) -> 
                              if is_leftrec then (BatSet.empty,true) else 
                              (if flag then (BatSet.add Epsilon fst,is_leftrec) else (fst,is_leftrec))
                            )
                            ) 
                            )
                        p (BatSet.empty,false))
                      else (exi,false);;

let rec get_first2: symbol list -> FIRST.t -> symbol BatSet.t->symbol BatSet.t
= fun lst first ret-> 
                  match lst with hd::tl -> (let hdfst=(FIRST.find hd first) in
                  let flag=(BatSet.mem Epsilon hdfst) in
                  let hdfst=(BatSet.remove Epsilon hdfst) in
                  if flag then (get_first2 tl first (BatSet.union hdfst ret)) else (BatSet.union hdfst ret))
                  |_-> (BatSet.add Epsilon ret);;


let rec is_nont : symbol ->symbol list->bool
= fun x lst -> match lst with hd::tl -> if hd=x then true else (is_nont x tl) 
                |_-> false;;

let rec get_follow: symbol list->symbol list -> FOLLOW.t->FIRST.t->FOLLOW.t
= fun nlst b follow first -> match b with hd::tl ->(
              if is_nont hd nlst then 
              (if tl=[] then follow else 
                let fset= (BatSet.remove Epsilon (get_first2 tl first BatSet.empty)) in
                let follow = (FOLLOW.add_set hd fset follow) in 
                (get_follow nlst tl follow first))
              else (get_follow nlst tl follow first)
                )
                |_-> follow;;
let rec get_follow2: symbol->symbol list->symbol list -> FOLLOW.t->FIRST.t->FOLLOW.t
= fun a nlst b follow first -> match b with hd::tl ->(
              if is_nont hd nlst then 
              (if tl=[] then follow else 
                let fset= (get_first2 tl first BatSet.empty) in
                if (BatSet.mem Epsilon fset) then 
                let follow = (FOLLOW.add_set hd (FOLLOW.find a follow) follow) in 
                (get_follow2 a nlst tl follow first)
                else (get_follow2 a nlst tl follow first)
                )
              else (get_follow2 a nlst tl follow first)
                )
                |_-> follow;;
let rec get_last: symbol list ->symbol
= fun lst -> match lst with hd::tl -> (if tl=[] then hd else get_last tl)
         |_->Epsilon;;
let check_LL1 : cfg -> bool
=fun g -> match g with (nlst,tlst,s,plst) ->  
          let first= (list_fold (fun x y ->FIRST.add x x y) tlst FIRST.empty) in
          let (first,is_leftrec)= (list_fold (fun x (fst,is_leftrec) -> 
                      let (fstx,is_left) = (get_first x plst fst BatSet.empty) in
                      let fst=(FIRST.add_set x fstx fst) in
                      (fst,is_leftrec || is_left)
            ) nlst (first,false)) in if is_leftrec then false 

          else (
            let follow = FOLLOW.empty in
            let follow = (FOLLOW.add s End follow) in
            let follow = 
              (list_fold (fun p f -> match p with (_,lst)->
                    (get_follow nlst lst f first)

                ) plst follow) in
            let follow = (list_fold (fun p f -> match p with (s,lst)->
                    let b=(get_last lst) in
                    if (is_nont b nlst) && b<>s then 
                      let fols=(FOLLOW.find s f) in (FOLLOW.add_set b fols f) 
                    else f
                  ) 
                  plst follow 
              ) in
              let follow = 
                (list_fold (fun p f -> match p with (s,lst)->
                      (get_follow2 s nlst lst f first)
  
                  ) plst follow) in
                  let follow = 
                    (list_fold (fun p f -> match p with (_,lst)->
                          (get_follow nlst lst f first)
      
                      ) plst follow) in
                  let follow = (list_fold (fun p f -> match p with (s,lst)->
                          let b=(get_last lst) in
                          if (is_nont b nlst) && b<>s then 
                            let fols=(FOLLOW.find s f) in (FOLLOW.add_set b fols f) 
                          else f
                        ) 
                        plst follow 
                    ) in
                    let follow = 
                      (list_fold (fun p f -> match p with (s,lst)->
                            (get_follow2 s nlst lst f first)
        
                        ) plst follow) in
              let par= 
                (list_fold (fun p par -> match p with (s,lst)->
                      let fst = (BatSet.remove Epsilon (get_first2 lst first BatSet.empty)) in 
                      (BatSet.fold
                        (fun a y -> ParsingTable.add (s,a) p y)  fst par
                      )
                  )plst ParsingTable.empty ) in
              let par= 
                (list_fold (fun p par -> match p with (s,lst)->
                      let fst =(get_first2 lst first BatSet.empty) in 
                      if (BatSet.mem Epsilon fst) then 
                      (BatSet.fold 
                        (fun b y -> (ParsingTable.add (s,b) p y))
                        (FOLLOW.find s follow) par
                      ) else par
                  )plst par ) in 
              let res = (ParsingTable.foldi 
                (fun _ pset flag -> 
                    let cnt=(BatSet.cardinal pset) in
                    (if cnt>=2 then false else flag)
                )
                par true 
              ) in res
          );;

let get_LL1 : cfg -> ParsingTable.t
=fun g -> match g with (nlst,tlst,s,plst) ->  
          let first= (list_fold (fun x y ->FIRST.add x x y) tlst FIRST.empty) in
          let (first,_)= (list_fold (fun x (fst,is_leftrec) -> 
                      let (fstx,is_left) = (get_first x plst fst BatSet.empty) in
                      let fst=(FIRST.add_set x fstx fst) in
                      (fst,is_leftrec || is_left)
            ) nlst (first,false)) in 
            let (first,_)= (list_fold (fun x (fst,is_leftrec) -> 
              let (fstx,is_left) = (get_first x plst fst BatSet.empty) in
              let fst=(FIRST.add_set x fstx fst) in
              (fst,is_leftrec || is_left)
           ) nlst (first,false)) in 
    
           (
            let follow = FOLLOW.empty in
            let follow = (FOLLOW.add s End follow) in
            let follow = 
              (list_fold (fun p f -> match p with (_,lst)->
                    (get_follow nlst lst f first)

                ) plst follow) in
            let follow = (list_fold (fun p f -> match p with (s,lst)->
                    let b=(get_last lst) in
                    if (is_nont b nlst) && b<>s then 
                      let fols=(FOLLOW.find s f) in (FOLLOW.add_set b fols f) 
                    else f
                  ) 
                  plst follow 
              ) in
              let follow = 
 
                (list_fold (fun p f -> match p with (s,lst)->
                 
                (get_follow2 s nlst lst f first)
                 
                 
                ) plst follow) 
             in
             let follow = 
              (list_fold (fun p f -> match p with (_,lst)->
                    (get_follow nlst lst f first)

                ) plst follow) in
            let follow = (list_fold (fun p f -> match p with (s,lst)->
                    let b=(get_last lst) in
                    if (is_nont b nlst) && b<>s then 
                      let fols=(FOLLOW.find s f) in (FOLLOW.add_set b fols f) 
                    else f
                  ) 
                  plst follow 
              ) in
              let follow = 
 
                (list_fold (fun p f -> match p with (s,lst)->
                 
                (get_follow2 s nlst lst f first)
                 
                 
                ) plst follow) 
             in
              let par= 
                (list_fold (fun p par -> match p with (s,lst)->
                      let fst = (BatSet.remove Epsilon (get_first2 lst first BatSet.empty)) in 
                      (BatSet.fold
                        (fun a y -> ParsingTable.add (s,a) p y)  fst par
                      )
                  )plst ParsingTable.empty ) in
              let par= 
                (list_fold (fun p par -> match p with (s,lst)->
                      let fst =(get_first2 lst first BatSet.empty) in 
                      if (BatSet.mem Epsilon fst) then 
                      (BatSet.fold 
                        (fun b y -> (ParsingTable.add (s,b) p y))
                        (FOLLOW.find s follow) par
                      ) else par
                  )plst par ) 
              
              in par
          );;

let rec parse2 : ParsingTable.t -> symbol list ->symbol list -> bool
= fun table input stack -> 
    
    match input with a::itl ->(
    match stack with x::stl ->

    if x=End then (a=End) else 
      (
        if x=a then (parse2 table itl stl) else
        let p=(ParsingTable.find (x,a) table) in
        if (BatSet.is_empty p) then false else(
          let (_,y) =BatSet.choose p in
       
              (parse2 table input (y@stl)))
            )
    |_-> true)
    |_->true;;
let parse : cfg -> symbol list -> bool
=fun cfg lst -> match cfg with (_,_,s,_)->

  let table = (get_LL1 cfg) in 

  (parse2 table (lst@[End]) (s::[End]));;
