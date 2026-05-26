import Datalog.Utils

inductive Term where
  | const : String → Term
  | var : String → Term
  deriving BEq

instance : ToString Term where
  toString
    | .const s | .var s => s

structure Atom where
  rel : String
  terms : List Term
  deriving BEq

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

def Term.isConst : Term → Bool
  | .const _ => true
  | _ => false

def Term.isVar : Term → Bool
  | .var _ => true
  | _ => false

def Term.isGround : Term → Bool :=
  Term.isConst

def Atom.isGround (atom : Atom) : Bool :=
  ∀ t ∈ atom.terms, t.isGround

def Rule.isGround (rule : Rule) : Bool :=
  rule.head.isGround ∧ ∀ a ∈ rule.body, a.isGround

def Rule.isFact (rule : Rule) : Bool :=
  rule.body.isEmpty

abbrev Substitution := String → String

def Atom.applySub (atom : Atom) (σ : Substitution) : Atom :=
  let terms := atom.terms.map fun
    | .const s => .const s
    | .var s => .const (σ s)
  Atom.mk atom.rel terms

abbrev Predicate := String × Nat

def Atom.predicate (atom : Atom) : Predicate :=
  (atom.rel, atom.terms.length)

def Program.Predicates (prog : Program) (pred : Predicate) : Prop :=
  ∃ r ∈ prog, pred = r.head.predicate ∨ ∃ a ∈ r.body, pred = a.predicate

example : Program.Predicates [Program| parent(xerces, brooke).] ("parent", 2) := by
  simp [Program.Predicates, Atom.predicate]

def Program.Constants (prog : Program) (t : Term) : Prop :=
  t.isConst ∧ ∃ r ∈ prog, t ∈ r.head.terms ∨ ∃ a ∈ r.body, t ∈ a.terms

example : Program.Constants [Program| parent(xerces, brooke).] [Term| brooke] := by
  simp [Program.Constants, Term.isConst]

def Program.HerbrandBase (prog : Program) (a : Atom) : Prop :=
  prog.Predicates a.predicate ∧ ∀ t ∈ a.terms, prog.Constants t

example : Program.HerbrandBase [Program| parent(xerces, brooke). parent(brooke, damocles).] [Atom| parent(damocles, xerces)] := by
  simp [Program.HerbrandBase, Program.Predicates, Atom.predicate, Program.Constants, Term.isConst]

inductive Program.HerbrandModel (prog : Program) : Atom → Prop where
  | step : {r : Rule} → r ∈ prog → (σ : Substitution) → ({a : Atom} → a ∈ r.body → prog.HerbrandModel (a.applySub σ)) → prog.HerbrandModel (r.head.applySub σ)

example : Program.HerbrandModel [Program| parent(xerces, brooke).] [Atom| parent(xerces, brooke)] := by
  let prog : Program := [Program| parent(xerces, brooke).]
  have h : [Rule| parent(xerces, brooke).] ∈ prog := by simp [prog]
  let σ : Substitution := fun _ => ""
  apply Program.HerbrandModel.step h σ
  grind

example : Program.HerbrandModel [Program| parent(xerces, brooke). ancestor(X, Y) :- parent(X, Y).] [Atom| ancestor(xerces, brooke)] := by
  let prog := [Program| parent(xerces, brooke). ancestor(X, Y) :- parent(X, Y).]
  suffices Program.HerbrandModel prog [Atom| parent(xerces, brooke)] by
    have h : [Rule| ancestor(X, Y) :- parent(X, Y).] ∈ prog := by simp [prog]
    let σ : Substitution := fun | "X" => "xerces" | "Y" => "brooke" | _ => ""
    apply Program.HerbrandModel.step h σ
    intro a ha
    simp at ha
    grind [Atom.applySub]
  have h : [Rule| parent(xerces, brooke).] ∈ prog := by simp [prog]
  let σ : Substitution := fun _ => ""
  apply Program.HerbrandModel.step h σ
  grind

def Rule.getPredicates (rule : Rule) : List Predicate :=
  rule.head.predicate :: rule.body.map Atom.predicate

def Program.getPredicates (prog : Program) : List Predicate :=
  prog.flatMap Rule.getPredicates |>.eraseDups

#eval Program.getPredicates [Program|
parent(xerces, brooke).
parent(brooke, damocles).
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
]

def Atom.getConstants (atom : Atom) : List String :=
  atom.terms.filterMap fun
    | .const s => some s
    | _ => none

def Rule.getConstants (rule : Rule) : List String :=
  rule.head.getConstants ++ rule.body.flatMap Atom.getConstants

def Program.getConstants (prog : Program) : List String :=
  prog.flatMap Rule.getConstants |>.eraseDups

#eval Program.getConstants [Program|
parent(xerces, brooke).
parent(brooke, damocles).
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
]

def Program.getHerbrandBase (prog : Program) : List Atom :=
  prog.getPredicates.flatMap (fun (rel, arity) =>
    prog.getConstants.product arity |>.map (List.map Term.const) |>.map (fun terms => Atom.mk rel terms))
  |>.eraseDups

#eval Program.getHerbrandBase [Program|
parent(xerces, brooke).
parent(brooke, damocles).
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
]
