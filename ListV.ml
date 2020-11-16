type ide = string;;

(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = 
  function x -> if x = i then v else applyenv r x;;

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

    | Estring of string		
    | Dict of (ide * exp) list      (*Espressione dizionario				  *)
    | DictAccess of evT * ide       (*Accesso tramite chiave   :      (Dict, Key)		  *)
    | AddInDict of evT * ide * exp  (*Inserimento chiave-valore:      (Dict, NewKey, NewValue)*)
    | RmDict of evT * ide		(*Rimozione tramite chiave :      (Dict, Key)		  *)
    | Clr of evT			(*Rimozione contenuto dizionario: (Dict)		  *)
    | ApplyOver of exp * evT        (*Applicazione funzione:	  (Fun, Dict)		  *)

(*tipi esprimibili*)

and evT =
      Int of int 
    | Bool of bool 
    | String of string
    | Unbound 
    | FunVal of evFun 
    | RecFunVal of ide * evFun

    (*Valori dizionario*)
    | ElemDict of evT	(*Singolo elemento				       *)
    | DictVal of dictval    (*Crea un dizionario evT, data una serie di valori evT.*)

    (*Valore di definizioni di funzioni valutate con scope dinamico*)
    |FunValD of evFunD
    |RecFunValD of ide * evFunD

and dictval = (ide * evT) list
(*Valore di una definizione di una funzione: chiusura*)
and evFun = ide * exp * evT env
(*Valore di una definizione di una funzione: Scope dinamico*)
and evFunD = ide * exp;;

(*rts*)
(*type checking*)
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
  |_ -> failwith("Not a valid type");;

(*funzioni di supporto*)
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

(*Funzione di supporto che converte un evT in exp, 
  se questo è un valore intero, booleano o una stringa.
  Questa funzione è utile per l'applicazione della funzione
  passata all'ApplyOver sugli elementi del dizionario*)
let toexp (a : evT) = match a with
  |Int(q) -> Eint(q)
  |Bool(q) -> Ebool(q)
  |String(q) -> Estring(q)
  |_ -> failwith("Convert error");;

(*interprete*)
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

  (*Creazione dizionario*)
  |Dict(a) -> let rec scan a1 = match a1 with
                |[] -> []
                |(b1,b2)::xs -> (b1, eval b2 r)::(scan xs)
      in DictVal(scan a)

  |AddInDict(d, id, v) ->   (*Fa uso di una funzione di appoggio per scandire il dizionario (Insert),
                              Una funzione di appoggio per considerare ogni elemento come una coppia (k,v) (reflect),
                              ed una variabile d'appoggio per valutare ricorsivamente tutto il dizionario (newDict) *)
      (let rec insert l = match l with
          |DictVal([]) -> [id, eval v r](*Elemento non trovato -> lo aggiunge *)
          |DictVal(x::xs) -> (let rec reflect x1 = match x1 with
                                |(a,b)-> (*Se la chiave corrisponde a quella da inserire -> exception*)
                                    if a=id then failwith("Chiave gia presente") 
                                    else (a, b)
                              in let newDict = DictVal(xs)
                              in (reflect x)::(insert newDict))
          |_ -> failwith("Type error")
       in DictVal(insert (d)))

  |RmDict(d, id) ->   (*Utilizza una funzione interna per scandire il dizionario
                        ed una per valutare ogni espressione del dizionario
                        Se non trova la chiave, solleva eccezione, 
                        altrimenti restituisce il dizionario senza quella coppia*)
      (let rec remove dicty = 
         match dicty with
           |DictVal([]) -> failwith("Chiave non presente")
           |DictVal((a,b)::xs)-> if a = id 
               then (*Valuta ogni elemento di xs*)
                 (let rec scan di = match di with
                     |[] -> []
                     |(c1,c2)::ys -> (c1, c2)::(scan ys)
                  in scan xs)
               else let newdict = DictVal(xs) in (a, b)::(remove newdict)
           |_ -> failwith("Type error")
       in DictVal(remove (d)))

  |Clr(d) -> DictVal([])

  |ApplyOver(f,d) ->  (*Utilizza una prima funzione interna che scandisce il dizionario
                        ed una che restituisce la coppia (k, f(v)).
                        Calcola quindi il valore di ogni elemento, scandendo ricorsivamente
                        il resto del dizionario con una variabile d'appoggio.*)
      (let rec scan l = match l with
          |DictVal([]) -> []
          |DictVal(x::xs) -> let rec apply x1 = match x1 with
                               |(a,b)-> (a, eval (FunCall(f,toexp(b))) r)
              in 
              let newdictionary = DictVal(xs)
              in (apply x)::(scan newdictionary)
          |_ -> failwith("Type error")
       in DictVal(scan (d)))

  |DictAccess(a, i) -> (*accede all'elemento con chiave i in a.
                         se non è presente, solleva eccezione. *)
      let rec valuta b = 
        match b with
          |DictVal([]) -> failwith("Elemento non presente")
          |DictVal([(a,c)]) -> if a = i then ElemDict(c)
              else failwith("Elemento non presente")
          |DictVal((a,c)::xs) -> if a = i then ElemDict(c)
              else (let newdict = DictVal(xs) 
                    in valuta newdict)
          |_ -> failwith("Type error")
      in valuta (a);;

(*===================================================================================================================*)
(*=========== Interprete che valuta seguendo regole di scope dinamico, valutando tutto nello stesso ambiente ========*)
(*===================================================================================================================*)

let rec rt_eval (e : exp) (r : evT env) : evT = match e with
    Eint n -> Int n 
  |Ebool b -> Bool b 
  |IsZero a -> iszero (rt_eval a r) 
  |Den i -> applyenv r i
  |Eq(a, b) -> eq (rt_eval a r) (rt_eval b r) 
  |Prod(a, b) -> prod (rt_eval a r) (rt_eval b r) 
  |Sum(a, b) -> sum (rt_eval a r) (rt_eval b r) 
  |Diff(a, b) -> diff (rt_eval a r) (rt_eval b r) 
  |Minus a -> minus (rt_eval a r) 
  |And(a, b) -> et (rt_eval a r) (rt_eval b r) 
  |Or(a, b) -> vel (rt_eval a r) (rt_eval b r) 
  |Not a -> non (rt_eval a r) 
  |Ifthenelse(a, b, c) -> 
      let g = (rt_eval a r) in
        if (typecheck "bool" g) 
        then (if g = Bool(true) then (rt_eval b r) else (rt_eval c r))
        else failwith ("nonboolean guard") 
  |Let(i, e1, e2) -> rt_eval e2 (bind r i (rt_eval e1 r))
  |Fun(i, a) -> FunValD(i, a) 
  |FunCall(f, eArg) -> 
      let fClosure = (rt_eval f r) in
        (match fClosure with
            FunValD(arg, fBody) -> 
              rt_eval fBody (bind r arg (rt_eval eArg r)) 
          |RecFunValD(g, (arg, fBody)) -> 
              let aVal = (rt_eval eArg r) in
              let rEnv = (bind r g fClosure) in
              let aEnv = (bind rEnv arg aVal) in
                rt_eval fBody aEnv 
          |_ -> failwith("non functional value")) 
  |Letrec(f, funDef, letBody) ->
      (match funDef with
          Fun(i, fBody) -> let r1 = (bind r f (RecFunValD(f, (i, fBody)))) in
              rt_eval letBody r1 
        |_ -> failwith("non functional def"))

  (*Valutazione stringhe*)
  |Estring(a) -> String(a)

  (*Creazione dizionario*)
  |Dict(a) -> let rec scan a1 = match a1 with
                |[] -> []
                |(b1,b2)::xs -> (b1, rt_eval b2 r)::(scan xs)
      in DictVal(scan a)
  |AddInDict(d, id, v) ->  (*Fa uso di una funzione di appoggio per scandire il dizionario (Insert),
                             Una funzione di appoggio per considerare ogni elemento come una coppia (k,v) (reflect),
                             ed una variabile d'appoggio per valutare ricorsivamente tutto il dizionario (newDict) *)
      (let rec insert l = match l with
          |DictVal([]) -> [id,rt_eval v r](*Elemento non trovato -> lo aggiunge *)
          |DictVal(x::xs) -> (let rec reflect x1 = match x1 with
                                |(a,b)-> (*Se la chiave corrisponde a quella da inserire -> exception*)
                                    if a=id then failwith("Chiave gia presente") 
                                    else (a,b)
                              in let newDict = DictVal(xs)
                              in (reflect x)::(insert newDict))
          |_ -> failwith("Type error")
       in DictVal(insert (d)))

  |RmDict(d, id) -> (*Utilizza una funzione interna per scandire il dizionario
                      ed una per valutare ogni espressione del dizionario
                      Se non trova la chiave, solleva eccezione, 
                      altrimenti restituisce il dizionario senza quella coppia*)
      (let rec remove dicty = 
         match dicty with
           |DictVal([]) -> failwith("Chiave non presente")
           |DictVal((a,b)::xs)-> if a = id 
               then (*Valuta ogni elemento di xs*)
                 (let rec scan di = match di with
                     |[] -> []
                     |(c1,c2)::ys -> (c1, c2)::(scan ys)
                  in scan xs)
               else let newdict = DictVal(xs) in (a, b)::(remove newdict)
           |_ -> failwith("Type error")
       in DictVal(remove (d)))

  |Clr(d) -> DictVal([])

  |ApplyOver(f,d) ->  (*Utilizza una prima funzione interna che scandisce il dizionario
                        ed una che restituisce la coppia (k, f(v)).
                        Calcola quindi il valore di ogni elemento, scandendo ricorsivamente
                        il resto del dizionario con una variabile d'appoggio.*)
      (let rec scan l = match l with
          |DictVal([]) -> []
          |DictVal(x::xs) -> let rec apply x1 = match x1 with
                               |(a,b)-> (a, rt_eval (FunCall(f,toexp(b))) r)
              in 
              let newdictionary = DictVal(xs)
              in (apply x)::(scan newdictionary)
          |_ -> failwith("Type error")
       in DictVal(scan (d)))

  |DictAccess(a, i) -> (*accede all'elemento con chiave i in a.
                         se non è presente, solleva eccezione. *)
      let rec valuta b = 
        match b with
          |DictVal([]) -> failwith("Elemento non presente")
          |DictVal([(a,c)]) -> if a = i then ElemDict(c)
              else failwith("Elemento non presente")
          |DictVal((a,c)::xs) -> if a = i then ElemDict(c)
              else (let newdict = DictVal(xs) 
                    in valuta newdict)
          |_ ->failwith("type error")
      in valuta (a);;
		
(*================================ Test ================================*)

(* basico: no let *)
let env0 = emptyenv Unbound;;

let e1 = FunCall(Fun("y", Sum(Den "y", Eint 1)), Eint 3);;

eval e1 env0;;

let e2 = FunCall(Let("x", Eint 2, Fun("y", Sum(Den "y", Den "x"))), Eint 3);;

eval e2 env0;;

(*========================== Test sui dizionari ==========================*)

let env1 = emptyenv Unbound;;

(*Creazione dizionari*)
let dec0 = Dict([("Nome1", Estring("Marco"));("Nome2", Estring("Elena"))]);; (*Dizionario d1 con 2 stringhe*)

let d0 = eval dec0 env1;;

let dec1 = Dict([("Eta1", Eint(22));("Eta2", Eint(24))]);;	  (*Dizionario d2 con 2 interi*)

let d1 = eval dec1 env1;;

(*Accesso ad un elemento*)

let acc0 = DictAccess(d0, "Nome1");;  (*Accesso al valore con chiave Nome1 del primo dizionario*)

eval acc0 env1;;

(*Inserimento elemento*)

let add0 = AddInDict(d0, "Matricola1", Eint(531466));; (*Aggiunge un campo intero al primo dizionario*)

let d3 = eval add0 env1;;

(*Rimozione elemento*)

let rem0 = RmDict(d3, "Nome2");;	    (*Rimuove l'elemento con chiave Nome1 dal primo dizionario*)

eval rem0 env1;;

(*Eliminazione contenuto dizionario*)

let clear = Clr(d0);;			      (*Svuota dizionario*)

let d4 = eval clear env1;;

(*Applica funzione correttamente ad ogni membro *)

let fun0 = Fun("y", Sum(Den "y", Eint 1));;    (*Incrementa di una unità il valore dell'argomento (intero)*)

let apply0 = ApplyOver(fun0, d1);;			(*Incrementa entrambe le 2 età contenute nel dizionario*)

eval apply0 env1;;

(*Operazioni composte
  Access(Add(Apply(Remove(Dictionary))))
  .[(Primo elemento : 15);(Secondo elemento : 30);(Terzo elemento : 60)]
  .[(Primo elemento : 15);(Terzo elemento : 60)]
  .[(Primo elemento : 30);(Terzo elemento : 120)]
  .[(Primo elemento : 30);(Secondo elemento (reinserito) : 30);(Terzo elemento : 120)]
  . -> 30
*)

let funtext = Fun ("x", Prod(Den "x", Eint(2)));;

let zero = eval (Dict([("Primo elemento", Eint(15));("Secondo elemento", Eint(30));("Terzo elemento", Eint(60))])) env1;;
let one  = eval (RmDict(zero, "Secondo elemento")) env1;;
let two  = eval (ApplyOver(funtext, one)) env1;;
let three= eval (AddInDict(two, "Secondo elemento (reinserito)", Eint(30))) env1;;
let four = eval (DictAccess(three, "Secondo elemento (reinserito)")) env1;;

(*================================ Test-cases non conformi ========================================*)

(*Creazione dizionario con tipi errati
  let test0 = Dict([("Test0", Minus(Ebool(true)))]);;
  eval test0 env1;;

  (*Accesso a chiave inesistente*)
  let test1 = DictAccess(d0, "Cognome");;
  eval test1 env1;;

  (*Inserimento chiave già presente*)
  let test2 = AddInDict(d0,"Nome1", Estring("Orazio"));;
  eval test2 env1;;

  (*Rimozione chiave inesistente*)
  let test3 = RmDict(d0, "Nome3");;
  eval test3 env1;;

  (*Applicazione di funzione su tipi non conformi*)
  let test4 = ApplyOver(fun0, d0);;
  eval test4 env1;;*)

(*==================================Test sulla parte opzionale====================================*)

(*Applico la stessa funzione con scope statico e con scope dinamico
  let x = 5;;
  let g z = z*x in
  let f y = let x = y + 5 in g (x*y) in f 5;;
*)
let ambiente = emptyenv Unbound;;

let funzioneDiTesting = 
  Let("x",Eint 5,
      Let("g",Fun("z",Prod(Den "z",Den "x")),
          Let("f",
              Fun("y",
                  Let("x",Sum(Den "y",Eint 5),
                      FunCall(Den "g",Prod(Den "x",Den "y")))),
              FunCall(Den "f",Eint 5))));;

eval funzioneDiTesting ambiente;;    (*Risultato atteso: 250*)

rt_eval funzioneDiTesting ambiente;; (*Risultato atteso: 500*)
