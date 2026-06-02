import Datalog.Syntax

declare_syntax_cat datalog_term
declare_syntax_cat datalog_atom
declare_syntax_cat datalog_rule
declare_syntax_cat datalog_prog

syntax ident : datalog_term
syntax ident ("(" datalog_term,* ")")? : datalog_atom
syntax datalog_atom (":-" datalog_atom,*)? "." : datalog_rule
syntax datalog_rule* : datalog_prog

syntax "[Term|" datalog_term "]" : term
syntax "[Atom|" datalog_atom "]" : term
syntax "[Rule|" datalog_rule "]" : term
syntax "[Prog|" datalog_prog "]" : term

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
  | `([Prog| $[$prog:datalog_rule]*]) =>
    `([ $[[Rule| $prog]],* ])

#check [Prog|
parent(xerces, brooke).
parent(brooke, damocles).
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
]
