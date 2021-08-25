(*
   RE - A regular expression library

   Copyright (C) 2001 Jerome Vouillon
   email: Jerome.Vouillon@pps.jussieu.fr

   This library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation, with
   linking exception; either version 2.1 of the License, or (at
   your option) any later version.

   This library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with this library; if not, write to the Free Software
   Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
*)

(*
What we could (should?) do:
- a* ==> longest ((shortest (no_group a)* ), a | ())  (!!!)
- abc understood as (ab)c
- "((a?)|b)" against "ab" should not bind the first subpattern to anything

Note that it should be possible to handle "(((ab)c)d)e" efficiently
*)
module Re = Core

exception Parse_error
exception Not_supported

let parse newline s =
  let i = ref 0 in
  let l = String.length s in
  let eos () = !i = l in
  let test c = not (eos ()) && s.[!i] = c in
  let accept c = let r = test c in if r then incr i; r in
  let get () = let r = s.[!i] in incr i; r in
  let unget () = decr i in

  let rec regexp () = regexp' (branch ())
  and regexp' left =
    if accept '|' then regexp' (Re.alt [left; branch ()]) else left
  and branch () = branch' []
  and branch' left =
    if eos () || test '|' || test ')' then Re.seq (List.rev left)
    else branch' (piece () :: left)
  and piece () =
    let r = atom () in
    if accept '*' then Re.rep (Re.nest r) else
    if accept '+' then Re.rep1 (Re.nest r) else
    if accept '?' then Re.opt r else
    if accept '{' then
      match integer () with
        Some i ->
          let j = if accept ',' then integer () else Some i in
          if not (accept '}') then raise Parse_error;
          begin match j with
            Some j when j < i -> raise Parse_error | _ -> ()
          end;
          Re.repn (Re.nest r) i j
      | None ->
          unget (); r
    else
      r
  and atom () =
    if accept '.' then begin
      if newline then Re.notnl else Re.any
    end else if accept '(' then begin
      let r = regexp () in
      if not (accept ')') then raise Parse_error;
      Re.group r
    end else
    if accept '^' then begin
      if newline then Re.bol else Re.bos
    end else if accept '$' then begin
      if newline then Re.eol else Re.eos
    end else if accept '[' then begin
      if accept '^' then
        Re.diff (Re.compl (bracket [])) (Re.char '\n')
      else
        Re.alt (bracket [])
    end else
    if accept '\\' then begin
      if eos () then raise Parse_error;
      match get () with
        '|' | '(' | ')' | '*' | '+' | '?'
      | '[' | '.' | '^' | '$' | '{' | '\\' as c -> Re.char c
      |                 _                       -> raise Parse_error
    end else begin
      if eos () then raise Parse_error;
      match get () with
        '*' | '+' | '?' | '{' | '\\' -> raise Parse_error
      |                 c            -> Re.char c
    end
  and integer () =
    if eos () then None else
    match get () with
      '0'..'9' as d -> integer' (Char.code d - Char.code '0')
    |     _        -> unget (); None
  and integer' i =
    if eos () then Some i else
    match get () with
      '0'..'9' as d ->
        let i' = 10 * i + (Char.code d - Char.code '0') in
        if i' < i then raise Parse_error;
        integer' i'
    | _ ->
        unget (); Some i
  and bracket s =
    if s <> [] && accept ']' then s else begin
      let c = char () in
      if accept '-' then begin
        if accept ']' then Re.char c :: Re.char '-' :: s else begin
          let c' = char () in
          bracket (Re.rg c c' :: s)
        end
      end else
        bracket (Re.char c :: s)
    end
  and char () =
    if eos () then raise Parse_error;
    let c = get () in
    if c = '[' then begin
      if accept '=' then raise Not_supported
      else if accept ':' then begin
        raise Not_supported (*XXX*)
      end else if accept '.' then begin
        if eos () then raise Parse_error;
        let c = get () in
        if not (accept '.') then raise Not_supported;
        if not (accept ']') then raise Parse_error;
        c
      end else
        c
    end else
      c
  in
  let res = regexp () in
  if not (eos ()) then raise Parse_error;
  res

type opt = [`ICase | `NoSub | `Newline]

let re ?(opts = []) s =
  let r = parse (List.memq `Newline opts) s in
  let r = if List.memq `ICase opts then Re.no_case r else r in
  let r = if List.memq `NoSub opts then Re.no_group r else r in
  r

let compile re = Re.compile (Re.longest re)
let compile_pat ?(opts = []) s = compile (re ~opts s)

let rec pp ppf re = 
  match re with
    Core.Set set -> (
      match set with
        [a,b] when a = b -> Format.fprintf ppf "%a" Cset.pp_ascii set
      | _ -> Format.fprintf ppf "[%a]" Cset.pp_ascii set
    )
  | Sequence (re_list) ->
      Format.fprintf ppf "%a" (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf "") pp) re_list
  | Alternative re_alt ->
      Format.fprintf ppf "%a" (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf "|") pp) re_alt
  | Repeat (re, i , j_opt) -> (
    match i, j_opt with
      0, None    -> Format.fprintf ppf "%a*" pp re
    | 1, None    -> Format.fprintf ppf "%a+" pp re
    | 0, Some(1) -> Format.fprintf ppf "%a?" pp re
    | i, Some(j) when i = j -> Format.fprintf ppf "%a{%d}" pp re i
    | i, Some(j) -> Format.fprintf ppf "%a{%d,%d}" pp re i j
    | i, None    -> Format.fprintf ppf "%a{%d,}" pp re i
  )
  | Beg_of_word 
  | End_of_word -> failwith "no word delimiter in posix regex"
  | Beg_of_line 
  | Beg_of_str -> Format.fprintf ppf "^"
  | End_of_line
  | End_of_str -> Format.fprintf ppf "$"
  | Not_bound  -> failwith "no not bound in posix regex"
  | Last_end_of_line -> failwith "no last end of line in posix regex"
  | Start -> Format.fprintf ppf "/"
  | Stop  -> Format.fprintf ppf "/"
  | Sem (sem , re) -> (
    match sem with
    | `Longest  -> Format.fprintf ppf "%a" pp re
    | `Shortest -> Format.fprintf ppf "%a" pp re
    | `First    -> Format.fprintf ppf "%a" pp re
  )
  | Sem_greedy (sem_greedy , re) -> (
    match sem_greedy with
    | `Greedy     -> Format.fprintf ppf "%a" pp re
    | `Non_greedy -> Format.fprintf ppf "%a"  pp re)
  | Group re ->
    Format.fprintf ppf "(%a)" pp re 
  | No_group re 
  | Nest re
  | Case re
  | No_case re -> Format.fprintf ppf "%a" pp re
  | Intersection _ -> failwith "no intersection ?"
  | Complement re_list ->
     Format.fprintf ppf "[^%a]" (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf "") pp) re_list
  | Difference _-> failwith "no difference ?"
  | Pmark _ -> failwith "no Pmark ?"

let pp re = Format.asprintf "%a" pp re