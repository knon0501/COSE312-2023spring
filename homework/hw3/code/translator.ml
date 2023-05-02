
open Spy
open Lib.Util
open Spvm


let temp_var_index = ref 0
let label_index = ref 1
let new_temp_var() = temp_var_index := !temp_var_index + 1; ".t" ^ (string_of_int !temp_var_index)
let new_label() = label_index := !label_index + 1; !label_index

exception Not_Implemented of string
exception Error of string (* raise when syntax is beyond Spy *)




let rec list_car ch = 
  match ch with
  | "" -> []
  | ch ->Spy.Constant(CString(String.make 1 (String.get ch 0))) :: list_car (String.sub ch 1 (String.length ch - 1));;
let rec translate : Spy.program -> Spvm.program
=fun p -> let l = new_label() in
           match p with hd::tl ->
          (translate_stmt hd)@(translate tl)
   
          | _-> [(l,HALT)]

and translate_expr : Spy.expr -> Spvm.id*Spvm.program
= fun expr -> match expr with
  | Spy.BoolOp(boolop,exprlst) ->
    (
      match exprlst with hd::tl ->(
          match tl with [] -> (translate_expr hd)
          | _-> (
            let (t1,code1) = (translate_expr hd) in
            let (t2,code2) = (translate_expr (Spy.BoolOp(boolop,tl))) in
            let t3 = new_temp_var() in
            let l = new_label() in
            let op = (if boolop=Spy.And then Spvm.AND else Spvm.OR) in
            (t3,code1@code2@[(l,ASSIGNV(t3,op,t1,t2))])
          )
      )
      |_->let t=new_temp_var() in let l=new_label() in (t,[(l,COPYC(t,1))])


    )
  | Spy.BinOp(exp1,binop,exp2) ->
      let op =
      (
        match binop with
          | Spy.Add -> Spvm.ADD
          | Spy.Sub -> Spvm.SUB
          | Spy.Mod -> Spvm.MOD
          | Spy.Mult ->Spvm.MUL
          | Spy.Div -> Spvm.DIV
          | Spy.Pow -> Spvm.POW
      ) in
      let (t1,code1) = (translate_expr exp1) in
      let (t2,code2) = (translate_expr exp2) in
      let t3 = new_temp_var() in
      let l = new_label() in
      (t3,code1@code2@[(l,ASSIGNV(t3,op,t1,t2))])
  | Spy.Compare(exp1,cmpop,exp2) ->
    let op =
      (
        match cmpop with
          | Spy.Eq -> Spvm.EQ
          | Spy.NotEq -> Spvm.NEQ
          | Spy.Lt -> Spvm.LT
          | Spy.LtE ->Spvm.LE
          | Spy.Gt -> Spvm.GT
          | Spy.GtE -> Spvm.GE
      ) in
      let (t1,code1) = (translate_expr exp1) in
      let (t2,code2) = (translate_expr exp2) in
      let t3 = new_temp_var() in
      let l = new_label() in
      (t3,code1@code2@[(l,ASSIGNV(t3,op,t1,t2))])
  | Spy.UnaryOp(unaryop,exp) ->
    let op =
      (
        match unaryop with
          | Spy.Not -> Spvm.NOT
          | Spy.UAdd -> Spvm.UPLUS
          | Spy.USub-> Spvm.UMINUS
      ) in
      let (t1,code1) = (translate_expr exp) in
      let t2 = new_temp_var() in
      let l = new_label() in
      (t2,code1@[(l,ASSIGNU(t2,op,t1))])
  | Spy.IfExp(exp1,exp2,exp3) ->
    let (t2,code2) = (translate_expr exp1) in
    let (t1,code1) = (translate_expr exp2) in
    let (t3,code3) = (translate_expr exp3) in
    let l1 = new_label() in
    let l2 = new_label() in
    let l3 = new_label() in
    let l4 = new_label() in
    let l5 = new_label() in
    let l6 = new_label() in
    let l7 = new_label() in
    let l8 = new_label() in
    let t4 = new_temp_var() in
    (t4,code2@
        [(l1,CJUMP(t2,l3))]@
        [(l2,UJUMP(l5))]@
        [l3,SKIP]@
        code1@
        [(l7,COPY(t4,t1))]@
        [(l4,UJUMP(l6))]@
        [l5,SKIP]@
        code3@
        [l8,COPY(t4,t3)]@
        [l6,SKIP])
  | Spy.Constant(c) ->
    let t = new_temp_var() in
    let l = new_label() in
    let code =
      match c with
        | CInt(y) -> COPYC(t,y)

        | CString(y) -> COPYS(t,y)
        | CBool(y) -> COPYC(t,(if y = true then 1 else 0 ))
        | CNone -> COPYN(t)
      in
    (t,[(l,code)])
  | Spy.Subscript(exp1,exp2) ->
    let (t1,code1) = (translate_expr exp1) in
    let (t2,code2) = (translate_expr exp2) in
    let l = new_label() in
    let t3 = new_temp_var() in
    (t3,code1@code2@[(l,ITER_LOAD(t3,t1,t2))])
  | Spy.List(explst) ->
    (
    let l = new_label() in
    match explst with hd::tl ->
      let (t1,code1) = (translate_expr hd) in
      let (t2,code2) = (translate_expr (Spy.List(tl))) in
      (t2,code1@code2@[(l,LIST_INSERT(t2,t1))])
    | _-> let t = new_temp_var()  in (t,[(l,LIST_EMPTY(t))])
    )
  | Spy.Tuple(explst) ->
    (
    let l = new_label() in
    match explst with hd::tl ->
      let (t1,code1) = (translate_expr hd) in
      let (t2,code2) = (translate_expr (Spy.Tuple(tl))) in
      (t2,code1@code2@[(l,TUPLE_INSERT(t2,t1))])
    | _-> let t = new_temp_var() in (t,[(l,TUPLE_EMPTY(t))])
    )
  | Spy.Call(exp1,explst) ->
    (
      let (t1,code1) = (translate_expr exp1) in
      let (idlst,code2) =
        (
          list_fold
          (fun x (y,z) -> let (t2,code3) = (translate_expr x) in (y@[t2],z@code3))
          explst
          ([],[])
        ) in
      let t3 = new_temp_var() in
      let l = new_label() in
      (
        match exp1 with
          | Spy.Name(x) ->
            (
              match x with
                |"print" ->
                  let code3 =
                  (
                    list_fold
                    (
                      fun x y -> let l2=new_label() in
                      let l3 =new_label() in 
                      let l4 = new_label() in 
                      let b = new_temp_var() in 
                      y@[(l2,WRITE(x));(l3,COPYS(b," "));(l4,WRITE(b))]
                    )
                    idlst
                    []
                  ) in
                  let l2 = new_label() in
                  let l3 = new_label() in
                  let t4 = new_temp_var() in
                  (t3,code2@code3@[(l2,COPYS(t4,"\n"))]@[(l3,WRITE(t4))]@[(l,COPYN(t3))])
                |"input" ->
                  (t3,[(l,READ(t3))])
                |"len" ->
                  (
                    match idlst with hd::_ ->
                      (t3,code2@[(l,ITER_LENGTH(t3,hd))])
                    |_-> raise (Not_Implemented "error")
                  )
                |"int" ->
                  (
                    match idlst with hd::_ ->
                      (t3,code2@[(l,INT_OF_STR(t3,hd))])
                    |_->raise (Not_Implemented "error")
                  )
                |"range" ->
                  (
                    match idlst with lo::tl ->
                      (match tl with hi::_->
                        (t3,code2@[(l,RANGE(t3,lo,hi))])
                      |_->
                        let l2=new_label() in 
                        let z = new_temp_var() in 
                        (t3,code2@[(l2,COPYC(z,0));(l,RANGE(t3,z,lo))])
                      )
                    |_->raise (Not_Implemented "error")
                  )
                |"isinstance" ->
                  (
                    match explst with _::tl ->(
                      match tl with typ::_->(
                        match typ with Spy.Name(x) ->
                        (
                          match idlst with id::_ ->
                            (t3,code2@[(l,IS_INSTANCE(t3,id,x))])
                          |_->raise (Not_Implemented "error")
                        )
                        |_->raise (Not_Implemented "error")
                      )
                      |_->raise (Not_Implemented "error")
                    )
                    |_->raise (Not_Implemented "error")
                  )
                | _-> (t3,code1@code2@[(l,CALL(t3,t1,idlst))])
            )
          | _-> (t3,code1@code2@[(l,CALL(t3,t1,idlst))])
      )
    )
  | Spy.Name(id) ->

    let l = new_label() in
    (id,[(l,SKIP)])
  | Spy.Lambda(idlst,exp) ->
    let t1 = new_temp_var() in
    let l1 = new_label() in
    let (t2,code1) = (translate_expr exp) in
    let l2 = new_label() in
    (t1,[(l1,FUNC_DEF(t1,idlst,code1@[(l2,RETURN(t2))]))])

  | Spy.Attribute(exp,_) ->
    let (t1,code1) = (translate_expr exp) in
    let l1 = new_label() in
    let l2 = new_label() in
    let l3 = new_label() in
    let l4 = new_label() in
    let l5 = new_label() in

    let t2 = new_temp_var() in
    let code2 = [
      (l1,FUNC_DEF(t1^".append",["n"],
      [
        (l2,LIST_APPEND(t1,"n"));
        (l3,COPYN(t2));
        (l4,RETURN(t2))
      ]))] in
    let t3 = new_temp_var() in
    let code3 = [(l5,COPY(t3,t1^".append"))] in
    (t3,code1@code2@code3)

  | Spy.ListComp(exp,clst) ->
    let (t,code) = (translate_expr (Spy.List([]))) in
    let stmt = (translate_listcomp(t,exp,clst)) in
    let code2 = (translate_stmt stmt) in
    (t,code@code2)

and translate_listcomp : (identifier)*(Spy.expr)*(comprehension list) -> Spy.stmt
= fun (t,exp,clst) -> match clst with
    | (exp1,exp2,explst)::tl ->
      For(exp1,exp2,[If(BoolOp(And,explst),
      [translate_listcomp(t,exp,tl)]
      ,[Pass])])
    | _->
      Spy.Expr((Spy.Call(Spy.Attribute(Name(t),"append"),[exp])))


and translate_stmt : Spy.stmt -> Spvm.program
= fun stmt -> match stmt with
  | Spy.FunctionDef(id,idlst,stmtlst) ->
    let code = (list_fold (fun x y -> y@(translate_stmt x)) (stmtlst@[Spy.Return(None)]) []) in
    let l = new_label() in

    [(l,FUNC_DEF(id,idlst,code))]
  | Spy.Return(x) ->
    (
    let l =new_label() in
    match x with None ->
      let t = new_temp_var() in
      let l2 = new_label() in
      [(l2,COPYN(t));(l,RETURN(t))]
    | Some y -> let (t,code) = (translate_expr y) in
      code@[(l,RETURN(t))]
    )
  | Spy.If(exp,slst1,slst2) ->
    let (t1,code1) = (translate_expr exp) in
    let code2 = (list_fold (fun x y -> y@(translate_stmt x)) slst1 []) in
    let code3 = (list_fold (fun x y -> y@(translate_stmt x)) slst2 []) in
    let l2 = new_label() in
    let l3 = new_label() in
    let l4 = new_label() in
    let l5 = new_label() in
    let l6 = new_label() in
    let l1 = new_label()in
    code1@
    [(l1,CJUMP(t1,l2))]@
    [(l3,UJUMP(l5))]@
    [(l2,SKIP)]@
    code2@
    [(l4,UJUMP(l6))]@
    [(l5,SKIP)]@
    code3@
    [(l6,SKIP)]

  | Spy.While(exp,slst) ->
    let l1 =new_label() in
    let l2 =new_label() in
    let l3 =new_label() in
    let l4 =new_label() in
    let (t1,code1) = (translate_expr exp) in
    let code2 = (list_fold (fun x y -> y@(translate_stmt x)) slst []) in
    let code3 = (list_fold (fun x y ->
                let z=
                  (match x with
                    | (l,UJUMP(0)) ->  (l,UJUMP(l4))
                    | (l,UJUMP(-1)) -> (l,UJUMP(l1))
                    | _->x
                  ) in
                y@[z]
                ) code2 [] ) in

    [(l1,SKIP)]@
    code1@
    [(l2,CJUMPF(t1,l4))]@
    code3@
    [(l3,UJUMP(l1))]@
    [(l4,SKIP)]

  | Spy.Expr(exp) ->
    let (_,code) = (translate_expr exp) in code

  | Spy.Pass ->
    let l = new_label() in [(l,SKIP)]

  | Spy.Assert(exp) ->
    let (t,code) = (translate_expr exp) in
    let l = new_label() in
     code@[(l,ASSERT(t))]

  | Spy.AugAssign(exp1,op,exp2) ->
    let (t1,code1) = (translate_expr exp1) in
    let (t2,code2) = (translate_expr exp2) in
    let (t3,code3) = (translate_expr (Spy.BinOp(Spy.Name(t1),op,Spy.Name(t2)))) in
    let l =new_label() in
    code1@code2@code3@[(l,COPY(t1,t3))]

  | Spy.Break ->
    let l = new_label() in
    [(l,UJUMP(0))]
  | Spy.Continue ->
    let l =new_label() in
    [(l,UJUMP(-1))]

  | Spy.Assign(explst,exp) -> (
    match explst with

    | hd::tl -> 
      let (t,code)=(translate_expr exp) in 
      code@(translate_assign(hd,Name(t)))@(translate_stmt (Spy.Assign(tl,Name(t))))

    | _-> []
  )
  | Spy.For(exp1,exp2,slst) ->(
    let (t1,code4)= (translate_expr exp2) in
    let i = new_temp_var() in
    let n = new_temp_var() in
    let l1 =new_label() in
    let l2 =new_label() in
    let l3 = new_label() in
    let l4 =new_label() in
    let l5 = new_label() in
    let l6 = new_label() in
    let l7= new_label() in  
    let le =new_label() in
    let ls =new_label() in
    let t2 =new_temp_var() in
    let e =new_temp_var() in
    let code2 = (list_fold (fun x y -> y@(translate_stmt x)) slst []) in
    let code3 = (list_fold (fun x y ->
                let z=
                  (match x with
                    | (l,UJUMP(0)) ->  (l,UJUMP(le))
                    | (l,UJUMP(-1)) -> (l,UJUMP(ls))
                    | _->x
                  ) in
                y@[z]
                ) code2 [] ) in
    let code1 = (
      [
        (l1,COPYC(i,-1));
        (l2,ITER_LENGTH(n,t1));
        (ls,SKIP);
        (l6,ASSIGNC(i,ADD,i,1));
        (l3,ASSIGNV(t2,EQ,i,n));
        (l4,CJUMP(t2,le));
        (l5,ITER_LOAD(e,t1,i));

      ]@
      (translate_assign (exp1,Spy.Name(e)))@
      code3
    ) in
    code4@code1@[(l7,UJUMP(ls));(le,SKIP)]


  )


and translate_assign : Spy.expr*Spy.expr -> Spvm.program
= fun (lexp,rexp) ->
  match lexp with
  | Spy.Name(x)-> assign_val(x,rexp)
  | Spy.List(lexplst)->
    (
      match rexp with
        | Spy.List(rexplst) ->
          (
            match rexplst with
              | rhd::rtl ->
              (
                match lexplst with
                | lhd::ltl -> (translate_assign(lhd,rhd))@
                              (translate_assign(Spy.List(ltl),Spy.List(rtl)))
                | _->[]
              )
              | _->[]
          )
        | Spy.Tuple(rexplst) ->
          (
            match rexplst with
              | rhd::rtl ->
              (
                match lexplst with
                | lhd::ltl -> (translate_assign(lhd,rhd))@
                              (translate_assign(Spy.List(ltl),Spy.List(rtl)))
                | _->[]
              )
              | _->[]
          )
        | Spy.Name(a) ->
          (
            let l3 =new_label() in 
            let i = new_temp_var() in
            let code = (list_fold
              (fun x c ->
                let l1 = new_label() in
                let l2 = new_label() in
                let e =new_temp_var() in
          
                c@[(l1,ITER_LOAD(e,a,i))]@
                (translate_assign(x,Spy.Name(e)))@
                [(l2,ASSIGNC(i,ADD,i,1))]
              )
              lexplst
              [(l3,COPYC(i,0))]
            ) in
            code
          )
        | Spy.Constant(CString(x)) ->
          (
            let lst =(list_car x) in 
            let x = (Spy.List(lst)) in 
            (translate_assign(lexp,x))
          )
        |_->(raise (Not_Implemented "error"))
    )
  | Spy.Tuple(lexplst)->
    (
      match rexp with
        | Spy.List(rexplst) ->
          (
            match rexplst with
              | rhd::rtl ->
              (
                match lexplst with
                | lhd::ltl -> (translate_assign(lhd,rhd))@
                              (translate_assign(Spy.List(ltl),Spy.List(rtl)))
                | _->[]
              )
              | _->[]
          )
        | Spy.Tuple(rexplst) ->
          (
            match rexplst with
              | rhd::rtl ->
              (
                match lexplst with
                | lhd::ltl -> (translate_assign(lhd,rhd))@
                              (translate_assign(Spy.List(ltl),Spy.List(rtl)))
                | _->[]
              )
              | _->[]
          )
        | Spy.Name(a) ->
          (
            let l3 =new_label() in 
            let i = new_temp_var() in
            let code = (list_fold
              (fun x c ->
                let l1 = new_label() in
                let l2 = new_label() in
                let e =new_temp_var() in
                c@[(l1,ITER_LOAD(e,a,i))]@
                (translate_assign(x,Spy.Name(e)))@
                [(l2,ASSIGNC(i,ADD,i,1))]
              )
              lexplst
              [(l3,COPYC(i,0))]
            ) in
            code
          )
          | Spy.Constant(CString(x)) ->
            (
              let lst =(list_car x) in 
              let x = (Spy.List(lst)) in 
              (translate_assign(lexp,x))
            )
        |_->(raise (Not_Implemented "error"))
    )
  |Spy.Subscript(x,y) ->

    let (a,code1) =(translate_expr x) in
    let (b,code2) = (translate_expr y ) in
    let (c,code3) = (translate_expr rexp) in 
    let l = new_label() in 
 
    code1@code2@code3@[(l,ITER_STORE(a,b,c))]

  |_->(raise (Not_Implemented "error"))


and assign_val : (identifier)*Spy.expr -> Spvm.program
= fun (x,exp) ->
  let l = new_label() in
  let (t,code) = (translate_expr exp) in
  code@[(l,COPY(x,t))]
