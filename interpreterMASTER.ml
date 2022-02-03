(* util functions *)

let is_lower_case c =
  'a' <= c && c <= 'z'

let is_upper_case c =
  'A' <= c && c <= 'Z'

let is_alpha c =
  is_lower_case c || is_upper_case c

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

let disj (p1 : 'a parser) (p2 : 'a parser) : 'a parser =
  fun ls ->
  match p1 ls with
  | Some (x, ls)  -> Some (x, ls)
  | None -> p2 ls

let (<|>) = disj

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

(* part1 AST *)

type name = string

type const =
  | I of int
  | N of string
  | U

type cmd =
  | Push of const
  | Add
  | Sub
  | Mul
  | Div
  | Trace
  | Ifgz  of cmds * cmds

and cmds = cmd list

(* part1 parser *)

let reserved = [
  "Push";
  "Add";
  "Sub";
  "Mul";
  "Div";
  "Trace";
  "Let";
  "If";
  "Else";
  "Fun";
  "End";
]

let name : string parser =
  let* xs1 = many1 (satisfy (fun c -> is_alpha c || c = '_')) in
  let* xs2 = 
    many (satisfy (fun c ->
      is_alphanum c ||
      (c = '_') ||
      (c = '\'')))
  in
  let s = (implode xs1) ^ (implode xs2) in
  if List.exists (fun x -> x = s) reserved
  then fail
  else pure s << ws

let nat_parser () =
  let* n = natural in
  pure (I n) << ws

let name_parser () =
  let* n = name in
  pure (N n)

let unit_parser () =
  let* _ = keyword "()" in
  pure (U)

let const_parser () =
  nat_parser () <|>
  name_parser () <|>
  unit_parser ()

let rec push_parser () =
  let* _ = keyword "Push" in
  let* cst = const_parser () in
  pure (Push cst)

and add_parser () =
  let* _ = keyword "Add" in
  pure (Add)

and sub_parser () =
  let* _ = keyword "Sub" in
  pure (Sub)

and mul_parser () =
  let* _ = keyword "Mul" in
  pure (Mul)

and div_parser () =
  let* _ = keyword "Div" in
  pure (Div)

and trace_parser () =
  let* _ = keyword "Trace" in
  pure (Trace)

and ifgz_parser () =
  let* _ = keyword "If" in
  let* cmds1 = cmds_parser () in
  let* _ = keyword "Else" in
  let* cmds2 = cmds_parser () in
  let* _ = keyword "End" in
  pure (Ifgz (cmds1, cmds2))

and cmd_parser () = 
  push_parser () <|>
  add_parser () <|>
  sub_parser () <|>
  mul_parser () <|>
  div_parser () <|>
  trace_parser () <|>
  ifgz_parser ()

and cmds_parser () =
  many (cmd_parser ())

let parse_cmds = parse (ws >> cmds_parser ())

(* interpreter *)

type value =
  | IVal of int
  | NVal of string
  | UVal

type stack = value list

type result =
  | Ok of stack
  | Error

let string_of_value v =
  match v with
  | IVal n -> string_of_int n
  | NVal s -> s
  | UVal -> "()"

let string_of_result res =
  match res with
  | Ok (v :: _) -> string_of_value v
  | _ -> "Error"

let string_of_log log = 
  let rec loop log =
    match log with
    | [] -> ""
    | s :: [] -> s
    | s :: log -> s ^ "; " ^ loop log
  in
  "[" ^ loop log ^ "]"

let rec interp st cmds log =
  match cmds with
  | (Push (I n)) :: cmds ->
    interp ((IVal n) :: st) cmds log
  | (Push (N s)) :: cmds ->
    interp ((NVal s) :: st) cmds log
  | (Push U) :: cmds ->
    interp (UVal :: st) cmds log
  | Add :: cmds -> (
    match st with
    | IVal n :: IVal m :: st -> interp (IVal (m + n) :: st) cmds log
    | _ -> (Error, log))
  | Sub :: cmds -> (
    match st with
    | IVal n :: IVal m :: st -> interp (IVal (m - n) :: st) cmds log
    | _ -> (Error, log))
  | Mul :: cmds -> (
    match st with
    | IVal n :: IVal m :: st -> interp (IVal (m * n) :: st) cmds log
    | _ -> (Error, log))
  | Div :: cmds -> (
    match st with
    | IVal 0 :: IVal _ :: _ -> (Error, log)
    | IVal n :: IVal m :: st -> interp (IVal (m / n) :: st) cmds log
    | _ -> (Error, log))
  | Trace :: cmds -> (
    match st with
    | v :: st -> interp (UVal :: st) cmds (string_of_value v :: log)
    | _ -> (Error, log))
  | Ifgz (cmds1, cmds2) :: cmds -> (
    match st with
    | IVal n :: st ->
      if n > 0
      then interp st (cmds1 @ cmds) log
      else interp st (cmds2 @ cmds) log
    | _ -> (Error, log))
  | [] -> (Ok st, log)

(* end of parser combinators *)

(* Interprets a program written in the Part1 Stack Language.
 * Required by the autograder, do not change its type. *)
let interpreter src =
  match parse_cmds src with
  | Some (cmds, []) -> (
    match interp [] cmds [] with
    | Ok (v :: _), logs -> (string_of_value v, logs)
    | _ -> ("Error", []))
  | _ -> ("Error", [])

(* Testing function. *)
let main fname = 
  let src = readlines fname in
  let (res, log) = interpreter src in
  print_endline (res ^ " " ^ string_of_log log)

  type name = string

  type const =
    | I of int
    | N of string
    | U 
  
  type cmd =
  | Push of const
  | Add
  | Sub
  | Mul
  | Div
  | Trace
  | Ifgz  of cmds * cmds
  
  | Let
  | Lookup
  | Block of cmds
  | FunCMD   of string * string * cmds 
  | Call 
  
  and cmds = cmd list 
  
  type term =
    (* lambda calculus *)
    | Name  of name
    | Fun   of name * name * term
    | App   of term * term
    (* extensions *)
    | Ifgz  of term * term * term
    | LetIn of name * term * term
    | Unit
    | Int   of int
    | Add   of term * term
    | Sub   of term * term
    | Mul   of term * term
    | Div   of term * term
    | Trace of term
  
  (* parser for term language *)
  
  (* util functions *)
  
  let is_lower_case c =
    'a' <= c && c <= 'z'
  
  let is_upper_case c =
    'A' <= c && c <= 'Z'
  
  let is_alpha c =
    is_lower_case c || is_upper_case c
  
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

(* compiler *)
  
let reserved = [
  "fun";
  "if";
  "then";
  "else";
  "let";
  "rec";
  "in";
  "trace";
  "main";
]

let name : string parser =
  let* xs1 = many1 (satisfy (fun c -> is_alpha c || c = '_')) in
  let* xs2 = 
    many (satisfy (fun c ->
      is_alphanum c ||
      (c = '_') ||
      (c = '\'')))
  in
  let s = (implode xs1) ^ (implode xs2) in
  if List.exists (fun x -> x = s) reserved
  then fail
  else pure s << ws

let name_parser () =
  let* n = name in
  pure (Name n)

let unit_parser () =
  let* _ = keyword "()" in
  pure (Unit)

let int_parser () =
  let* n = natural in
  pure (Int n) << ws

let rec term_parser0 () =
  let* _ = pure () in
  (name_parser ()) <|>
  (unit_parser ()) <|>
  (int_parser ()) <|>
  (keyword "(" >> term_parser () << keyword ")")

and term_parser1 () =
  let* es = many1 (term_parser0 ()) in
  match es with
  | e :: es ->
    pure (List.fold_left (fun acc e -> App (acc, e)) e es)
  | _ -> fail

and term_parser2 () =
  let* e = term_parser1 () in
  let opr () = 
    (let* _ = keyword "*" in
    let* e = term_parser1 () in
    pure ((fun e1 e2 -> Mul (e1, e2)), e))
    <|>
    (let* _ = keyword "/" in
    let* e = term_parser1 () in
    pure ((fun e1 e2 -> Div (e1, e2)), e))
  in
  let* es = many (opr ()) in
  pure (List.fold_left (fun acc (f, e) -> f acc e) e es)

and term_parser3 () =
  let* e = term_parser2 () in
  let opr () = 
    (let* _ = keyword "+" in
    let* e = term_parser2 () in
    pure ((fun e1 e2 -> Add (e1, e2)), e))
    <|>
    (let* _ = keyword "-" in
    let* e = term_parser2 () in
    pure ((fun e1 e2 -> Sub (e1, e2)), e))
  in
  let* es = many (opr ()) in
  pure (List.fold_left (fun acc (f, e) -> f acc e) e es)

and term_parser () = 
  let* _ = pure () in
  (keyword "trace" >> term_parser3 () >|= (fun e -> Trace e)) <|>
  (fun_parser ()) <|>
  (iflz_parser ()) <|>
  (letrec_parser ()) <|>
  (letin_parser ()) <|>
  (term_parser3 ())

and fun_parser () =
  let* _ = keyword "fun" in
  let* a = name in
  let* _ = keyword "->" in
  let* e = term_parser () in
  pure (Fun ("_", a, e))

and iflz_parser () =
  let* _ = keyword "if" in
  let* cond = term_parser () in
  let* _ = keyword "then" in
  let* e1 = term_parser () in
  let* _ = keyword "else" in
  let* e2 = term_parser () in
  pure (Ifgz (cond, e1, e2))

and letin_parser () =
  let* _ = keyword "let" in
  let* n = name in
  let* _ = keyword "=" in
  let* e1 = term_parser () in
  let* _ = keyword "in" in
  let* e2 = term_parser () in
  pure (LetIn (n, e1, e2))

and letrec_parser () =
  let* _ = keyword "let" in
  let* _ = keyword "rec" in
  let* n = name in
  let* args = many1 name in
  let* _ = keyword "=" in
  let* e1 = term_parser () in
  let (e1, _) =
    List.fold_right
      (fun arg (acc, len) ->
        let fn = if len = 1 then n else "_" in
        (Fun (fn, arg, acc), len - 1))
      args (e1, List.length args)
  in
  let* _ = keyword "in" in
  let* e2 = term_parser () in
  pure (LetIn (n, e1, e2))

(* Parse programs written in the term language. *)
let parse_prog (s : string) : (term * char list) option = 
  parse (ws >> term_parser ()) s 

let termToListOfCmds (t : term) : cmd list = 
  let rec aux (t : term) (accum : cmd list) : cmd list =
    match t with 
    | Int i -> Push (I i) :: accum 
    | Name name -> Push (N name) :: Lookup :: accum 
    | Unit -> Push (U) :: accum 
    | Trace name -> (aux name accum @ [Trace]) @ accum 
    | Add (left, right) -> (aux left accum) @ (aux right accum) @ Add :: accum 
    | Sub (left, right) -> (aux left accum) @ (aux right accum) @ Sub :: accum 
    | Mul (left, right) -> (aux left accum) @ (aux right accum) @ Mul :: accum 
    | Div (left, right) -> (aux left accum) @ (aux right accum) @ Div :: accum 
    | LetIn (name, preIN, postIN) -> [Block ([Push (N name)] @ aux preIN accum @ [Let] @ aux postIN accum)] 
    | App (name, argument) -> aux name accum @ aux argument accum @ Call :: accum
    | Ifgz (condition, expr1, expr2) -> aux condition accum @ [Ifgz ([Block (aux expr1 accum)], [Block(aux expr2 accum)])] 
    | Fun (name, argument, cmd) -> [FunCMD (name, argument, aux cmd accum)] @ [Push (N name)] @ [Lookup] @ accum   
  in aux t [] 

let rec cmdsToString (commands : cmds) : string =  
    match commands with 
      | [] -> "" 
      | Push (I i) :: rest -> " Push" ^ " " ^ string_of_int i ^ " " ^ (cmdsToString rest) 
      | Push (N name) :: rest -> " Push" ^ " " ^ name ^ " " ^ (cmdsToString rest)
      | Push (U) :: rest -> " Push ()" ^ " " ^ (cmdsToString rest) 
      | Add :: rest -> " Add" ^ " " ^ (cmdsToString rest) 
      | Sub :: rest -> " Sub" ^ " " ^ (cmdsToString rest)
      | Mul :: rest -> " Mul" ^ " " ^ (cmdsToString rest) 
      | Div :: rest -> " Div" ^ " " ^ (cmdsToString rest) 
      | Trace :: rest -> " Trace" ^ " " ^ (cmdsToString rest)
      | Lookup :: rest -> " Lookup" ^ " " ^ (cmdsToString rest)
      | Let :: rest -> " Let" ^ " " ^ (cmdsToString rest)
      | Call :: rest -> " Call" ^ " " ^ (cmdsToString rest)
      | Block (commands) :: rest -> " Begin" ^ " " ^ cmdsToString commands ^ " " ^ "End" ^ " " ^ cmdsToString rest 
      | FunCMD (name, argument, commands) :: rest -> " Fun" ^ " " ^ name ^ " " ^ argument ^ " " ^ cmdsToString commands ^ " " ^ "End" ^ " " ^ cmdsToString rest
      | Ifgz (beforeIF, afterIF) :: rest -> " If" ^ " " ^ cmdsToString beforeIF ^ " " ^ "Else" ^ " " ^ cmdsToString afterIF ^ " " ^ "End" ^ " " ^ cmdsToString rest 
      
let compiler (src : string) : string = 
  match parse_prog src with
  | Some (term, list) -> cmdsToString (termToListOfCmds term)
  | None -> "" 