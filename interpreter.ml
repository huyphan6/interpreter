(* util functions *)

let is_lower_case c =
  'a' <= c && c <= 'z'

let is_upper_case c =
  'A' <= c && c <= 'Z'

let is_alpha c =
  is_lower_case c || is_upper_case c || c = '_'

let is_digit c =
  '0' <= c && c <= '9'

let is_alphanum c =
  is_lower_case c ||
  is_upper_case c ||
  is_digit c

let is_blank c =
  String.contains " \012\n\r\t" c

let explode s =
  List.of_seq (String.to_seq s)

let implode ls =
  String.of_seq (List.to_seq ls)

let readlines (file : string) : string =
  let fp = open_in file in
  let rec loop () =
    match input_line fp with
    | s -> s ^ "\n" ^ (loop ())
    | exception End_of_file -> ""
  in
  let res = loop () in
  let () = close_in fp in
  res

(* end of util functions *)

(* parser combinators *)

type 'a parser = char list -> ('a * char list) option

let parse (p : 'a parser) (s : string) : ('a * char list) option =
  p (explode s)

let pure (x : 'a) : 'a parser =
  fun ls -> Some (x, ls)

let fail : 'a parser = fun ls -> None

let bind (p : 'a parser) (q : 'a -> 'b parser) : 'b parser =
  fun ls ->
    match p ls with
    | Some (a, ls) -> q a ls
    | None -> None

let (>>=) = bind
let (let*) = bind

let read : char parser =
  fun ls ->
  match ls with
  | x :: ls -> Some (x, ls)
  | _ -> None

let satisfy (f : char -> bool) : char parser =
  fun ls ->
  match ls with
  | x :: ls ->
    if f x then Some (x, ls)
    else None
  | _ -> None

let char (c : char) : char parser =
  satisfy (fun x -> x = c)

let seq (p1 : 'a parser) (p2 : 'b parser) : 'b parser =
  fun ls ->
  match p1 ls with
  | Some (_, ls) -> p2 ls
  | None -> None

let (>>) = seq

let seq' (p1 : 'a parser) (p2 : 'b parser) : 'a parser =
  fun ls ->
  match p1 ls with
  | Some (x, ls) ->
    (match p2 ls with
     | Some (_, ls) -> Some (x, ls)
     | None -> None)
  | None -> None

let (<<) = seq'

let alt (p1 : 'a parser) (p2 : 'a parser) : 'a parser =
  fun ls ->
  match p1 ls with
  | Some (x, ls)  -> Some (x, ls)
  | None -> p2 ls

let (<|>) = alt

let map (p : 'a parser) (f : 'a -> 'b) : 'b parser =
  fun ls ->
  match p ls with
  | Some (a, ls) -> Some (f a, ls)
  | None -> None

let (>|=) = map

let (>|) = fun p c -> map p (fun _ -> c)

let rec many (p : 'a parser) : ('a list) parser =
  fun ls ->
  match p ls with
  | Some (x, ls) ->
    (match many p ls with
     | Some (xs, ls) -> Some (x :: xs, ls)
     | None -> Some (x :: [], ls))
  | None -> Some ([], ls)

let rec many1 (p : 'a parser) : ('a list) parser =
  fun ls ->
  match p ls with
  | Some (x, ls) ->
    (match many p ls with
     | Some (xs, ls) -> Some (x :: xs, ls)
     | None -> Some (x :: [], ls))
  | None -> None

let rec many' (p : unit -> 'a parser) : ('a list) parser =
  fun ls ->
  match p () ls with
  | Some (x, ls) ->
    (match many' p ls with
     | Some (xs, ls) -> Some (x :: xs, ls)
     | None -> Some (x :: [], ls))
  | None -> Some ([], ls)

let rec many1' (p : unit -> 'a parser) : ('a list) parser =
  fun ls ->
  match p () ls with
  | Some (x, ls) ->
    (match many' p ls with
     | Some (xs, ls) -> Some (x :: xs, ls)
     | None -> Some (x :: [], ls))
  | None -> None

let whitespace : unit parser =
  fun ls ->
  match ls with
  | c :: ls ->
    if String.contains " \012\n\r\t" c
    then Some ((), ls)
    else None
  | _ -> None

let ws : unit parser =
  (many whitespace) >| ()

let ws1 : unit parser =
  (many1 whitespace) >| ()

let digit : char parser =
  satisfy is_digit

let natural : int parser =
  fun ls ->
  match many1 digit ls with
  | Some (xs, ls) ->
    Some (int_of_string (implode xs), ls)
  | _ -> None

let literal (s : string) : unit parser =
  fun ls ->
  let cs = explode s in
  let rec loop cs ls =
    match cs, ls with
    | [], _ -> Some ((), ls)
    | c :: cs, x :: xs ->
      if x = c
      then loop cs xs
      else None
    | _ -> None
  in loop cs ls

let keyword (s : string) : unit parser =
  (literal s) >> ws >| ()
  
(* end of parser combinators *)

(* Interprets a program written in the Part1 Stack Language.
 * Required by the autograder, do not change its type. *)

type const = Nat of int | Name of string | Unit | Function of string * string * prog * int (* closure is a type of function *)

                                                  (* Fucntion of name * arguement * commands * scope End *)

and env = Env of (string * const * int) 

and com = 
  | Push of const
  | Trace 
  | Add
  | Sub
  | Mul
  | Div 
  | Let
  | Lookup 
  | BEND
  | CEND 
  | FunDef of (string * string * prog)
  | Call 
  | Begin of prog
  | IfElse of (prog * prog) and prog = com list 

and stack = const list 
and log = string list

let constToString (c : const) : string = 
  match c with 
  | Name x -> x
  | Nat y -> string_of_int y
  | Unit -> "()"
  | _ -> "<fun>"

let char2 : char parser =
  satisfy is_alpha

let traceParser : com parser =
  let* _ = keyword "Trace" in
  pure Trace

let addParser : com parser =
  let* _ = keyword "Add" in
  pure Add

let subParser : com parser =
  let* _ = keyword "Sub" in
  pure Sub

let mulParser : com parser =
  let* _ = keyword "Mul" in
  pure Mul

let divParser : com parser =
  let* _ = keyword "Div" in
  pure Div

let letParser : com parser = 
  let* _ = keyword "Let" in
  pure Let

let lookupParser (): com parser = 
  let* _ = keyword "Lookup" in 
  pure Lookup

let callParser (): com parser = 
  let* _ = keyword "Call" in
  pure Call 

let rec comParser () : com parser = 
  pushParser () <|>
  traceParser <|>
  addParser <|>
  subParser <|>
  mulParser <|>
  divParser <|>
  letParser <|>
  ifElseEndParser () <|>
  beginEndParser () <|>
  closureParser () <|>
  lookupParser () <|>
  callParser ()

and ifElseEndParser (): com parser = 
  let* _ = keyword "If" in 
  let* iftrue = many (ws >> comParser()) in 
  let* _ = keyword "Else" in 
  let* iffalse = many (ws >> comParser ()) in 
  let* _ = keyword "End" in 
  pure (IfElse (iftrue, iffalse))  

and beginEndParser (): com parser = 
  let* _ = keyword "Begin" in 
  let* inner = many (comParser()) in
  let* _ = keyword "End" in 
  pure(Begin inner)

and closureParser (): com parser = 
  let* _ = keyword "Fun" in 
  let* funName = ws >> constParser () in
  let* arg = ws >> constParser () in
  let* commands = progParser () in 
  let* _ = keyword "End" in 
  pure(FunDef(constToString(funName), constToString(arg), commands)) 

and pushParser () : com parser = 
  let* _ = ws in 
  let* _ = keyword "Push" in
  let* cst = constParser () in
  let* _ = ws in 
  pure (Push cst)

and stringParser : const parser = 
  fun ls ->
    match many1 char2 ls with 
    | Some (xs, ls) -> Some (Name (implode xs), ls)
    | _ -> None

and natParser : const parser =
  fun ls ->
    match many1 digit ls with
    | Some (xs, ls) -> Some (Nat (int_of_string (implode xs)), ls)
    | _ -> None

and unitParser : const parser = 
  fun ls ->
    match ls with 
    | '(' :: ')' :: ls -> Some (Unit, ls)
    | _ -> None

and constParser () : const parser = 
  natParser <|> 
  stringParser <|>
  unitParser   

and progParser (): prog parser =
  let* com = comParser () in
  let* prog =
    many (
      let* _ = ws in
      comParser () )
  in pure (com :: prog) 

let isName n : bool =
  match n with 
  | Name n -> true
  | _ -> false

let string_of_log log = 
  let rec loop log = 
    match log with 
    | [] -> ""
    | s :: [] -> s
    | s :: log -> s ^ "; " ^ loop log
  in 
  "[ " ^ loop log ^ "]"

let rec getVarFromEnv (env : env list) (varName : string) (varScope : int) : const option = 
  match env with 
    | Env(name, value, scope) :: tail -> if name = varName && scope <= varScope then Some value else getVarFromEnv tail varName varScope (* x = 3, gets the 3 from x in the environment *)
    | [] -> None 

let rec addVar (scope : env list) (varName : string) (varValue : const) (varScope : int) : env list =
  match scope with 
    | Env (a, b, c) :: tail -> if a = varName then Env (varName, varValue, varScope)::tail else Env(a,b,c) :: addVar tail varName varValue varScope
    | [] -> [Env (varName, varValue, varScope)] 

let rec clearVars (env : env list) (prevScope : int) (newScope : env list) : env list = 
  match env with 
    | Env (a, b, c) :: tail -> if c = prevScope then clearVars tail prevScope newScope else clearVars tail prevScope (Env(a,b,c) :: newScope)
    | [] -> newScope 

(* *)

let rec getFunction (scope : const list) (funName : string) (funScope : int) : const option = 
  match scope with 
    | Function (a, b, c, d) :: tail -> if a = funName && d <= funScope then Some (Function (a,b,c,d)) else getFunction tail funName funScope  
    | _ -> None 

let rec addFunction (scope : const list) (funName : string) (funArg : string) (funCommands : prog) (funScope : int) : const list =
  match scope with 
    | Function (a, b, c, d) :: tail -> if a = funName && b = funArg then Function (funName, funArg, funCommands, funScope) :: Function(a,b,c,d) :: tail 
                                        else Function(a,b,c,d) :: addFunction tail funName funArg funCommands funScope 
    | [] -> [Function (funName, funArg, funCommands, funScope)] 
    | _ -> []

let rec clearFunction (functions : const list) (prevScope : int) (newScope : const list) : const list = 
  match functions with 
    | Function (a, b, c, d) :: tail -> if d = prevScope then clearFunction tail prevScope newScope else clearFunction tail prevScope (Function(a,b,c,d) :: newScope)
    | _ -> newScope

(*  *)

let popStack (stack : stack list) : stack =
  match stack with 
  | top :: tail -> top
  | [] -> []

let prevTopStack (stack : stack list) : stack list = 
  match stack with 
    | top :: tail -> tail 
    | [] -> []

let rec eval (p : prog) (s : stack) (l : log) (env : env list) (functionList : const list) (scope : int) (localStack : stack list): (string * string list) = 
  match p, s with 
  | Push cst :: p, _ -> eval p (cst :: s) l env functionList scope localStack 
  | Trace :: p, v :: s -> eval p (Unit :: s) (constToString(v) :: l) env functionList scope localStack
  | Trace :: p, [] -> ("Error", [])
  | Add :: p, Nat v2 :: Nat v1 :: s -> eval p ( Nat (v1 + v2) :: s) l env functionList scope localStack
  | Add :: p, _ -> ("Error",[])
  | Sub :: p, Nat v2 :: Nat v1 :: s -> eval p ( Nat(v1 - v2) :: s) l env functionList scope localStack
  | Sub :: p, _ -> ("Error",[])
  | Mul :: p, Nat v2 :: Nat v1 :: s -> eval p ( Nat(v1 * v2) :: s) l env functionList scope localStack
  | Mul :: p, _ -> ("Error",[])
  | Div :: p, Nat v2 :: Nat v1 :: s -> if v2 == 0 then ("Error", []) else (eval p ( Nat(v1 / v2) :: s)) l env functionList scope localStack
  | Div :: p, _ -> ("Error",[])

  | Let :: p, v2 :: Name (v1) :: s -> eval p s l (Env(v1,v2,scope)::env) functionList scope localStack
  | Let :: p,  [] -> ("Error", []) 
  | Let :: p, _ :: [] -> ("Error", []) 
  | Let :: p, _ :: _ -> ("Error", []) 

  | Lookup :: p, Name v1 :: s -> (match getVarFromEnv env v1 scope with 
                                  | Some value -> eval p (value::s) l env functionList scope localStack 
                                  | None -> (match getFunction functionList v1 scope with
                                              | Some x -> eval p (x :: s) l env functionList scope localStack
                                              | None -> ("Error", []))
                                  ) 
  | Lookup :: p, [] -> ("Error", [])
  | Lookup :: p, _ -> ("Error", [])

  | Begin (commands) :: p, s -> eval (commands @ [BEND] @ p) [] l env functionList (scope + 1) (s :: localStack) 
  | BEND :: p, v1 :: s -> eval p (v1 :: popStack localStack) l (clearVars env scope []) (clearFunction functionList scope []) (scope - 1) (prevTopStack localStack)
  | BEND :: p, _ -> ("Error", []) 

  | FunDef (name, args, commands) :: p, _ -> eval p s l env (addFunction functionList name args commands scope) scope localStack 

  | Call :: p, (arg :: Function(a,b,c,d) :: s) -> eval (c @ [CEND] @ p) [] l (Env(b,arg,scope) :: env) functionList (scope + 1) (s :: localStack) 
  | Call :: p, [] -> ("Error", [])
  | Call :: p, _::[] -> ("Error", []) 
  | Call :: p, _::_ -> ("Error", [])

  | CEND :: p, v1 :: s -> eval p (v1 :: popStack localStack) l env functionList (scope - 1) (prevTopStack localStack)
  | CEND :: p, _ -> ("Error", [])

  | IfElse (cmd1, cmd2) :: p, Nat (i) :: s -> if i > 0 then eval (cmd1 @ p) s l env functionList scope localStack else eval (cmd2 @ p) s l env functionList scope localStack
  | IfElse (cmd1, cmd2) :: p, _ -> ("Error", [])

  | [], Nat (top) :: tail -> (string_of_int top, l)  
  | [], Name (top) :: tail -> (top, l)
  | [], Unit :: tail -> ("()", l)
  | [], [] -> ("", l)
  | [], _ -> ("<fun>", l) 

let interpreter (src : string) : (string * string list) =
  match parse (progParser ()) src with 
  | Some (prog, []) -> eval prog [] [] [] [] 0 [[]] 
  | _ -> ("Error", []) 

let main read = 
  let src = readlines read in 
  let (res, log) = interpreter src in 
  print_endline( res ^ " " ^ string_of_log log) 