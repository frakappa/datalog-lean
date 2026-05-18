inductive Term where
  | const : String → Term
  | var : String → Term

instance : ToString Term where
  toString
    | .const s | .var s => s

structure Atom where
  rel : String
  terms : List Term

instance : ToString Atom where
  toString
    | Atom.mk rel [] => rel
    | Atom.mk rel terms => rel ++ "(" ++ ", ".intercalate (terms.map toString) ++ ")"

structure Rule where
  head : Atom
  body : List Atom

instance : ToString Rule where
  toString
    | Rule.mk head [] => toString head ++ "."
    | Rule.mk head body => toString head ++ " :- " ++ ", ".intercalate (body.map toString) ++ "."

abbrev Program := List Rule

instance : ToString Program where
  toString prog :=
    "\n".intercalate (prog.map toString)

#eval ([
  .mk (.mk "parent" [.const "xerces", .const "brooke"]) [],
  .mk (.mk "parent" [.const "brooke", .const "damocles"]) [],
  .mk (.mk "ancestor" [.var "X", .var "Y"]) [.mk "parent" [.var "X", .var "Y"]],
  .mk (.mk "ancestor" [.var "X", .var "Y"]) [.mk "parent" [.var "X", .var "Z"], .mk "ancestor" [.var "Z", .var "Y"]],
] : Program)

declare_syntax_cat datalog_term
declare_syntax_cat datalog_atom
declare_syntax_cat datalog_rule
declare_syntax_cat datalog_program

syntax ident : datalog_term
syntax ident ("(" datalog_term,* ")")? : datalog_atom
syntax datalog_atom (":-" datalog_atom,*)? "." : datalog_rule
syntax datalog_rule* : datalog_program

syntax "[Term|" datalog_term "]" : term
syntax "[Atom|" datalog_atom "]" : term
syntax "[Rule|" datalog_rule "]" : term
syntax "[Program|" datalog_program "]" : term

open Lean.Syntax (mkStrLit) in
macro_rules
  | `([Term| $s:ident]) =>
    let s := s.getId.toString
    if s.front.isUpper then
      `(Term.var $(mkStrLit s))
    else
      `(Term.const $(mkStrLit s))
  | `([Atom| $rel:ident]) =>
    `(Atom.mk $(mkStrLit rel.getId.toString) [])
  | `([Atom| $rel:ident ( $[$terms:datalog_term],* )]) =>
    `(Atom.mk $(mkStrLit rel.getId.toString) [ $[[Term| $terms]],* ])
  | `([Rule| $head:datalog_atom .]) =>
    `(Rule.mk [Atom| $head] [])
  | `([Rule| $head:datalog_atom :- $[$body:datalog_atom],* .]) =>
    `(Rule.mk [Atom| $head] [ $[[Atom| $body]],* ])
  | `([Program| $[$prog:datalog_rule]*]) =>
    `([ $[[Rule| $prog]],* ])

#check [Program|
parent(xerces, brooke).
parent(brooke, damocles).
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
]
