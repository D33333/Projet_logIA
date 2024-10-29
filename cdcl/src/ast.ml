type var = int

type lit = int

type model = int list

module Clause = Set.Make(
  struct type t = lit

  let compare x y =
    if abs x == abs y then 0
    else if abs x > abs y then 1 else -1
end)

module Cnf = Set.Make(
  struct type t = Clause.t

  let compare = Clause.compare
end)

type t = {
  nb_var: int;
  nb_clause: int;
  cnf: Cnf.t
}

let neg var = -var

type lab_clause = {
  c: Clause.t;
  label: int
}

module Lab_Cnf = Set.Make(
  struct type t = lab_clause

  let compare c1 c2 = Clause.compare c1.c c2.c
end)

type lab_t = {
  mutable nb_var_l: int;
  mutable nb_clause_l: int;
  mutable cnf_l: Lab_Cnf.t
}

type 'a printer = Format.formatter -> 'a -> unit

let pp_clause : Clause.t printer = fun fmt clause ->
  Clause.iter (fun v -> Format.fprintf fmt "%d " v) clause

let pp_cnf : Cnf.t printer = fun fmt cnf ->
  Cnf.iter (fun clause -> Format.fprintf fmt "%a0@." pp_clause clause) cnf

let pp : t printer = fun fmt t ->
  Format.fprintf fmt "p %d %d@." t.nb_var t.nb_clause;
  Format.fprintf fmt "%a@." pp_cnf t.cnf
