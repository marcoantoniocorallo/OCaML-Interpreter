(*Identificatori campi in dizionario*)
type ide = string;;

(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;	(* v valore di default*)
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = 
  function x -> if x = i then v else applyenv r x;;

(****Sintassi astratta****)
(*tipi algebrici*)
type exp = 
      Eint of int 
    | Ebool of bool 
    | Den of ide 
    | Prod of exp * exp 
    | Sum of exp * exp 
    | Diff of exp * exp 
    | Eq of exp * exp 
    | Minus of exp 
    | IsZero of exp 
    | Or of exp * exp 
    | And of exp * exp 
    | Not of exp 
    | Ifthenelse of exp * exp * exp 
    | Let of ide * exp * exp 
    | Fun of ide * exp 
    | FunCall of exp * exp 
    | Letrec of ide * exp * exp

    (*Valori dizionario*)
    | Estring of string		
    | Dict of edict		  (*Espressione dizionario				    *)
    | Get of exp * ide	  (*Accesso tramite chiave   :      (Dict, Key)		    *)
    | Add of exp * ide * exp  (*Inserimento chiave-valore:      (Dict, NewKey, NewValue)*)
    | Rm of exp * ide	  (*Rimozione tramite chiave :      (Dict, Key)		    *)
    | Clear of exp		  (*Rimozione contenuto dizionario: (Dict)		    *)
    | ApplyOver of exp * exp  (*Applicazione funzione:	  (Fun, Dict)		    *)
and edict = Empty | Elem of (ide * exp) * edict;;

(*tipi esprimibili*)
type evT =
      Int of int 
    | Bool of bool 
    | String of string
    | Unbound 
    | FunVal of evFun 
    | RecFunVal of ide * evFun

    (*Valori dizionario*)
    | ElemDict of evT	(*Singolo elemento				       *)
    | DictVal of dictval    (*Crea un dizionario evT, data una serie di valori evT.*)
and dictval = EmptyVal | ElemVal of (ide * evT) * dictval

(*Valore di una definizione di una funzione: chiusura*)
and evFun = ide * exp * evT env;;

(****RTS****)
(*type checking a run-time per controllare che: 
  • Gli argomenti delle operazioni aritmetiche e del test di uguaglianza siano valori numerici
  • La guardia di un condizionale sia una espressione booleana*)
let typecheck (s : string) (v : evT) : bool = match s with
    "int" -> (match v with
                 Int(_) -> true 
               |_ -> false) 
  |"bool" -> (match v with
                 Bool(_) -> true 
               |_ -> false) 
  |"string" -> (match v with
                   String(_) -> true
                 |_ ->false)
  |"dictval" -> (match v with
                    DictVal(_) -> true
                  |_ ->false)
  |_ -> failwith("Not a valid type");;

(*funzioni di supporto: fanno uso del type checking*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
           (Int(n),Int(u)) -> Int(n*u)
         | _-> failwith ("Type error"))
  else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
           (Int(n),Int(u)) -> Int(n+u)
         | _-> failwith ("Type error"))
  else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
           (Int(n),Int(u)) -> Int(n-u)
         | _-> failwith ("Type error"))
  else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
           (Int(n),Int(u)) -> Bool(n=u)
         | _-> failwith ("Type error"))
  else failwith("Type error");;

let minus x = if (typecheck "int" x) 
  then (match x with
           Int(n) -> Int(-n)
         | _-> failwith ("Type error"))
  else failwith("Type error");;

let iszero x = if (typecheck "int" x)
  then (match x with
           Int(n) -> Bool(n=0)
         | _-> failwith ("Type error"))
  else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
  then (match (x,y) with
           (Bool(b),Bool(e)) -> (Bool(b||e))
         | _-> failwith ("Type error"))
  else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
  then (match (x,y) with
           (Bool(b),Bool(e)) -> Bool(b&&e)
         | _-> failwith ("Type error"))
  else failwith("Type error");;

let non x = if (typecheck "bool" x)
  then (match x with
           Bool(true)  -> Bool(false) 
         | Bool(false) -> Bool(true)
         | _-> failwith ("Type error"))
  else failwith("Type error");;

(*Accede all'elemento con chiave key*)
let get dict key = if (typecheck "dictval" dict)
  then let rec f di = (match di with
                        |EmptyVal -> failwith("Campo non trovato")
                        |ElemVal((i, v), d) -> if i=key then v
                            else f d
                      ) 
    in match dict with
      |DictVal(elem) -> f elem
      |_ -> failwith("Type error")
  else failwith("Type error");;

(*Aggiunge l'elemento {k:v} al dizionario se non è già presente la chiave k*)
let add (d: evT) (k : ide) (v : evT) = if (typecheck "dictval" d)
  then let rec f d = (
         match d with
           |EmptyVal -> ElemVal((k, v),EmptyVal)
           |ElemVal((i,v'),d') -> 
               if i=k 
               then failwith("Chiave gia' presente")
               else ElemVal((i,v'),f d')
       )
    in match d with
      |DictVal(elem) -> DictVal(f elem)
      |_ -> failwith("Type error")
  else failwith("Type error");;

(*Rimuove elemento con chiave k. Se non è presente, lascia invariato il dizionario*)
let rm (d : evT) (k : ide) = if (typecheck "dictval" d)
  then let rec f d = (
         match d with
           |EmptyVal -> EmptyVal
           |ElemVal((i,v'),d') ->
               if i=k
               then f d'
               else ElemVal((i,v'), f d')
       )
    in match d with
      |DictVal(elem) -> DictVal(f elem)
      |_ -> failwith("Type error")
  else failwith("Type error");;

(****interprete****)
let rec eval (e : exp) (r : evT env) : evT = match e with
    Eint n -> Int n 
  |Ebool b -> Bool b 
  |IsZero a -> iszero (eval a r) 
  |Den i -> applyenv r i
  |Eq(a, b) -> eq (eval a r) (eval b r) 
  |Prod(a, b) -> prod (eval a r) (eval b r) 
  |Sum(a, b) -> sum (eval a r) (eval b r) 
  |Diff(a, b) -> diff (eval a r) (eval b r) 
  |Minus a -> minus (eval a r) 
  |And(a, b) -> et (eval a r) (eval b r) 
  |Or(a, b) -> vel (eval a r) (eval b r) 
  |Not a -> non (eval a r) 
  |Ifthenelse(a, b, c) -> 
      let g = (eval a r) in
        if (typecheck "bool" g) 
        then (if g = Bool(true) then (eval b r) else (eval c r))
        else failwith ("nonboolean guard") 
  |Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r))
  |Fun(i, a) -> FunVal(i, a, r) 
  |FunCall(f, eArg) -> 
      let fClosure = (eval f r) in
        (match fClosure with
            FunVal(arg, fBody, fDecEnv) -> 
              eval fBody (bind fDecEnv arg (eval eArg r)) 
          |RecFunVal(g, (arg, fBody, fDecEnv)) -> 
              let aVal = (eval eArg r) in
              let rEnv = (bind fDecEnv g fClosure) in
              let aEnv = (bind rEnv arg aVal) in
                eval fBody aEnv 
          |_ -> failwith("non functional value")) 
  |Letrec(f, funDef, letBody) ->
      (match funDef with
          Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
              eval letBody r1 
        |_ -> failwith("non functional def"))

  (*Valutazione stringa *)
  |Estring(a) -> String(a)
  (*Nuovo dizionario*)
  |Dict(d) -> let rec eval' a = match a with
                |Empty -> EmptyVal
                |Elem((i,e),a') -> ElemVal((i, eval e r), eval' a')
      in DictVal(eval' d)
  (*Estrai elemento*)
  |Get(d,id) -> get (eval d r) id
  (*Aggiunge {k:v} a d*)
  |Add(d,k,v) -> add (eval d r) k (eval v r)
  (*Rimuove elemento con chiave k se esiste*)
  |Rm(d,k) -> rm (eval d r) k
  (*Azzera il dizionario*)
  |Clear(d) -> (match (eval d r) with
                   DictVal(a) -> DictVal(EmptyVal)
                 |_ -> failwith("Type error"))
  (*Applica la funzione f ad ogni elemento di d. 
    Richiede che la funzione si possa applicare ad ogni elemento
    -> Dizionario omogeneo*)
  |ApplyOver(f, d) -> app (eval d r) f r

and app (d : evT) (f : exp) (r : evT env) : evT =
  let rec f' d = 
    match d with
      |EmptyVal -> EmptyVal
      |ElemVal((i,e),d') -> ElemVal((i, (eval (FunCall(f, (subst e))) r)), (f' d'))
  in 
    match d with
        DictVal(t) -> DictVal(f' t)
      |_ -> failwith("Type error")

and subst = function
  |Int(t)->Eint(t)
  |Bool(t)->Ebool(t)
  |String(t)->Estring(t)
  |_->failwith("type error")
;;

(****Test****)
let env0 = emptyenv Unbound;;

let e1 = FunCall(Fun("y", Sum(Den "y", Eint 1)), Eint 3);;
eval e1 env0;;

let e2 = FunCall(Let("x", Eint 2, Fun("y", Sum(Den "y", Den "x"))), Eint 3);;
eval e2 env0;;

(*Funzione ricorsiva: fattoriale*)
let body =
  Fun( "x",
       Ifthenelse( Eq( Den "x", Eint 0 ), 
                   Eint 1,
                   Prod( Den "x", FunCall(
                                    Den "fact", Diff( Den "x", Eint 1) ) ) 
                 ) 
     );;

(*Applico il fattoriale di 5: 120 *)
let fattoriale = Letrec( "fact", body, FunCall( Den "fact", Eint 5 ) );;
eval fattoriale (emptyenv Unbound);;

(*========================== Test sui dizionari ==========================*)

let env1 = emptyenv Unbound;;

(*Creazione dizionario: 3 campi di partenza*)
let dec0 = Dict(Elem(("Nome1", Estring("Marco")),
                     Elem(("Nome2", Estring("Elena")),
                          Elem(("Nome3",Estring("Filippo")),
                               Empty))));;
eval dec0 env1;; 

(*Accesso ad un elemento*)
let dec1 = Get(dec0,"Nome2");;
eval dec1 env1;;  

(*Inserimento elemento in dizionario*)
let dec2 = Add(dec0, "Nome4", Estring("Ciccio"));;
eval dec2 env1;;
eval (Get(dec2, "Nome4")) env1;;

(*Rimozione elemento da dizionario*)
let dec3 = Rm(dec2, "Nome4");;
eval dec3 env1;;

(*Resetta un dizionario*)
let dec4 = Clear(dec3);;
eval dec4 env1;;

(*Applica una funzione su un dizionario monomorfo*)
let dec5 = Dict(Elem(("Eta1", Eint(24)),
                     Elem(("Eta2", Eint(26)),
                          Empty)));;
let fun0 = Fun("y", Prod(Den "y", Eint 2));; (*Raddoppia i campi del dizionario*)
let apply0 = ApplyOver(fun0, dec5);;
eval apply0 env1;;

(*Operazioni composte
  Get(Add(Remove(ApplyOver(Dictionary))))
  .[(Primo elemento : 15);(Secondo elemento : 30);(Terzo elemento : 60)]
  .[(Primo elemento : 30);(Secondo elemento : 60);(Terzo elemento : 120)]
  .[(Primo elemento : 30);(Terzo elemento : 120)]
  .[(Primo elemento : 30);(Terzo elemento : 120);(Secondo elemento (reinserito) : 42)]
  . -> 42 *)
let funtext = Fun ("x", Prod(Den "x", Eint(2)));;

let zero = Dict(Elem(("Primo elemento", Eint(15)),
                     Elem(("Secondo elemento", Eint(30)),
                          Elem(("Terzo elemento", Eint(60)),
                               Empty))));;
let one  = Rm(zero, "Secondo elemento");;
let two= Add(one, "Secondo elemento (reinserito)", Eint(42));;
let three  = ApplyOver(funtext, two);;
let four = Get(three, "Secondo elemento (reinserito)");;
let five = eval four env1;;
