import Mathlib.Tactic

import Datalog.Utils

-- Aliases

abbrev Constant :=
  String

abbrev Variable :=
  String

abbrev Relation :=
  String

abbrev Arity :=
  Nat

abbrev Predicate :=
  Relation × Arity

-- Term

inductive Term where
  | const : Constant → Term
  | var : Variable → Term
  deriving DecidableEq

instance : ToString Term where
  toString
    | .const c => c
    | .var v => v

instance : Repr Term where
  reprPrec term _ := f!"{toString term}"

def Term.isConst : Term → Bool
  | .const _ => true
  | _ => false

def Term.isVar : Term → Bool
  | .var _ => true
  | _ => false

def Term.constant? : Term → Option Constant
  | .const c => some c
  | _ => none

def Term.variable? : Term → Option Variable
  | .var v => some v
  | _ => none

-- Atom

structure Atom where
  rel : Relation
  terms : List Term
  deriving DecidableEq

instance : ToString Atom where
  toString
    | Atom.mk rel [] => rel
    | Atom.mk rel terms => rel ++ "(" ++ ", ".intercalate (toString <$> terms) ++ ")"

instance : Repr Atom where
  reprPrec atom _ := f!"{toString atom}"

def Atom.predicate (atom : Atom) : Predicate :=
  (atom.rel, atom.terms.length)

def Atom.isGround (atom : Atom) : Bool :=
  ∀ t ∈ atom.terms, t.isConst

-- Rule

structure Rule where
  head : Atom
  body : List Atom
  deriving DecidableEq

instance : ToString Rule where
  toString
    | Rule.mk head [] => toString head ++ "."
    | Rule.mk head body =>
      toString head ++ " :- " ++ ", ".intercalate (toString <$> body)

instance : Repr Rule where
  reprPrec rule _ := f!"{toString rule}"

def Rule.isGround (rule : Rule) : Bool :=
  rule.head.isGround ∧ ∀ a ∈ rule.body, a.isGround

def Rule.isFact (rule : Rule) : Bool :=
  rule.body = ∅

-- Program

abbrev Program :=
  List Rule

instance : ToString Program where
  toString prog :=
    "\n".intercalate (toString <$> prog)

instance : Repr Program where
  reprPrec prog _ := f!"{toString prog}"

-- DSL

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
    if s.front.isUpper then `(Term.var $(mkStrLit s)) else `(Term.const $(mkStrLit s))
  | `([Atom| $rel:ident]) =>
    `(Atom.mk $(mkStrLit rel.getId.toString) [])
  | `([Atom| $rel:ident ( $[$terms:datalog_term],* )]) =>
    `(Atom.mk $(mkStrLit rel.getId.toString) [ $[[Term| $terms]],* ])
  | `([Rule| $head:datalog_atom .]) =>
    `(Rule.mk [Atom| $head] [])
  | `([Rule| $head:datalog_atom :- $[$body:datalog_atom],* .]) =>
    `(Rule.mk [Atom| $head] [ $[[Atom| $body]],* ])
  | `([Prog| $[$prog:datalog_rule]*]) =>
    `(([ $[[Rule| $prog]],* ] : Program))

#check [Prog|
parent(xerces, brooke).
parent(brooke, damocles).
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
]

-- Substitution

abbrev Substitution :=
  Variable → Constant

def Term.applySub (σ : Substitution) : Term → Term
  | .const c => .const c
  | .var v => .const (σ v)

def Atom.applySub (σ : Substitution) (atom : Atom) : Atom :=
  Atom.mk atom.rel (atom.terms.map (Term.applySub σ))

theorem Term.isConst_of_applySub {σ : Substitution} {term : Term} :
    term.applySub σ |>.isConst := by
  simp [Term.isConst, Term.applySub]
  cases term with simp

theorem Atom.isGround_of_applySub {σ : Substitution} {atom : Atom} :
    atom.applySub σ |>.isGround := by
  simp [Atom.isGround, Atom.applySub, Term.isConst_of_applySub]

-- Predicates

def Rule.predicates (rule : Rule) :=
  {rule.head.predicate} ∪ rule.body.toFinset.image Atom.predicate

def Program.predicates (prog : Program) : Finset Predicate :=
  prog.toFinset.biUnion Rule.predicates

#eval Program.predicates [Prog|
parent(xerces, brooke).
parent(brooke, damocles).
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
]

theorem Program.mem_predicates {prog : Program} :
    ∀ p, p ∈ prog.predicates ↔ ∃ r ∈ prog, p = r.head.predicate ∨ ∃ a ∈ r.body, p = a.predicate := by
  simp [Program.predicates, Rule.predicates]
  grind

-- Constants

def Atom.constants (atom : Atom) : Finset Term :=
  atom.terms.filter Term.isConst |>.toFinset

def Rule.constants (rule : Rule) : Finset Term :=
  rule.head.constants ∪ rule.body.toFinset.biUnion Atom.constants

def Program.constants (prog : Program) : Finset Term :=
  prog.toFinset.biUnion Rule.constants

#eval Program.constants [Prog|
parent(xerces, brooke).
parent(brooke, damocles).
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
]

theorem Program.mem_constants {prog : Program} :
    ∀ t, t ∈ prog.constants ↔ t.isConst ∧ ∃ r ∈ prog, t ∈ r.head.terms ∨ ∃ a ∈ r.body, t ∈ a.terms := by
  simp [Program.constants, Rule.constants, Atom.constants]
  grind

-- Herbrand base

def Program.hb (prog : Program) : Finset Atom :=
  prog.predicates.biUnion (fun (rel, arity) =>
    prog.constants.cartesianPower arity |>.image (fun terms =>
      Atom.mk rel terms))

#eval Program.hb [Prog|
parent(xerces, brooke).
parent(brooke, damocles).
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
]

theorem Program.mem_hb {prog : Program} :
    ∀ a, a ∈ prog.hb ↔ a.predicate ∈ prog.predicates ∧ ∀ t ∈ a.terms, t ∈ prog.constants := by
  intro a
  constructor <;> intro h
  · constructor
    · simp [Program.hb] at h
      obtain ⟨rel, arity, hpreds, tup, hconsts, htup⟩ := h
      simp [Program.mem_predicates, Atom.predicate] at *
      simp [Finset.mem_cartesianPower] at hconsts
      grind
    · intro t ht
      simp [Program.hb, Finset.mem_cartesianPower] at h
      grind
  · simp [Program.hb]
    use a.rel, a.terms.length
    constructor
    · exact h.left
    · use a.terms
      simp [Finset.mem_cartesianPower]
      exact h.right

-- Herbrand model

inductive Program.HM (prog : Program) : Atom → Prop where
  | cons : ∀ r ∈ prog, ∀ σ, (∀ a ∈ r.body, prog.HM (a.applySub σ)) → prog.HM (r.head.applySub σ)

def Program.hm (prog : Program) : Set Atom :=
  {atom | prog.HM atom}

-- Safety

def Rule.IsSafe (rule : Rule) : Prop :=
  ∀ t ∈ rule.head.terms, t.isVar → ∃ a ∈ rule.body, t ∈ a.terms

def Program.IsSafe (prog : Program) : Prop :=
  ∀ r ∈ prog, r.IsSafe

example : Program.IsSafe [Prog|
parent(xerces, brooke).
parent(brooke, damocles).
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
] := by simp [Program.IsSafe, Rule.IsSafe, Term.isVar]

-- Finiteness

theorem Program.hm_subset_hb {prog : Program} {safety : prog.IsSafe} :
    prog.hm ⊆ prog.hb := by
  intro _ h
  induction h with
  | cons r hr σ _ ih =>
    simp [Program.mem_hb]
    constructor
    · simp [Program.mem_predicates, Atom.predicate, Atom.applySub]
      grind
    · intro t ht
      simp [Program.mem_constants]
      constructor
      · suffices r.head.applySub σ |>.isGround by
          simp [Atom.isGround] at this
          exact this t ht
        exact Atom.isGround_of_applySub
      · cases Classical.em (t ∈ r.head.terms) with
        | inl hhead => exact ⟨r, hr, .inl hhead⟩
        | inr hhead =>
          have ⟨v, hv⟩ : ∃ s, .var s ∈ r.head.terms ∧ .const (σ s) = t := by
            simp [Atom.applySub, Term.applySub] at ht
            grind
          have ⟨a, ha⟩ := (safety r hr) (.var v) hv.left (by simp [Term.isVar])
          have ht' : t ∈ (a.applySub σ).terms := by
            simp [Atom.applySub, Term.applySub]
            grind
          simp [Program.mem_hb, Program.mem_constants] at ih
          grind

-- Fixpoint semantics

def Program.cons (prog : Program) (db : Set Atom) : Set Atom :=
  {atom | ∃ r ∈ prog, ∃ σ, r.head.applySub σ = atom ∧ ∀ a ∈ r.body, a.applySub σ ∈ db}

def Program.lfp (prog : Program) : Set Atom :=
  {atom | ∀ db, prog.cons db ⊆ db → atom ∈ db}

theorem cons_monotonic (prog : Program) :
    ∀ db₁ db₂, db₁ ⊆ db₂ → prog.cons db₁ ⊆ prog.cons db₂ := by
  intro db₁ db₂ h
  simp [Program.cons]
  intro a r hr σ hσ hbody
  use r, hr, σ, hσ
  intro a ha
  apply h
  exact hbody a ha

theorem Program.hm_eq_lfp {prog : Program} :
    prog.hm = prog.lfp := by
  ext
  constructor
  · intro h db hdb
    induction h with
    | cons r hr σ _ ih =>
      apply hdb
      exact ⟨r, hr, σ, rfl, ih⟩
  · intro h
    apply h
    intro a ⟨r, hr, σ, hσ, hbody⟩
    rw [← hσ]
    apply Program.HM.cons r hr σ hbody

-- Interpreter

abbrev SubstitutionC :=
  List (Variable × Constant)

def Term.applySubC (sub : SubstitutionC) : Term → Term
  | .const c => .const c
  | .var v => .const (sub.lookup v |>.getD "")

def Atom.applySubC (sub : SubstitutionC) (atom : Atom) : Atom :=
  Atom.mk atom.rel (atom.terms.map (Term.applySubC sub))

def SubstitutionC.toFun (sub : SubstitutionC) : String → String :=
  fun v => sub.lookup v |>.getD ""

theorem Term.applySubC_eq_applySub_toFun {term : Term} {sub : SubstitutionC} :
    term.applySubC sub = term.applySub sub.toFun := by
  simp [Term.applySubC, Term.applySub, SubstitutionC.toFun]

theorem Atom.applySubC_eq_applySub_toFun {atom : Atom} {sub : SubstitutionC} :
    atom.applySubC sub = atom.applySub sub.toFun := by
  simp [Atom.applySubC, Atom.applySub]
  intro t ht
  exact Term.applySubC_eq_applySub_toFun

def Atom.patternMatch (pattern target : Atom) (sub : SubstitutionC := []) : Option SubstitutionC :=
  if pattern.predicate = target.predicate then
    pattern.terms.zip target.terms |>.foldl (fun acc (t₁, t₂) =>
      match acc with
      | some sub =>
        match t₁, t₂ with
        | .const c₁, .const c₂ => if c₁ = c₂ then sub else none
        | .var v, .const c =>
          match sub.lookup v with
          | some c' => if c = c' then sub else none
          | none => (v, c) :: sub
        | _, _ => none
      | none => none
    ) (some sub)
  else
    none

#eval [Atom| parent(X, Y)].patternMatch [Atom| parent(xerces, brooke)]
#eval [Atom| parent(X, Y)].patternMatch [Atom| ancestor(xerces, brooke)]
#eval [Atom| parent(X, Y)].patternMatch [Atom| parent(xerces, brooke, damocles)]
#eval [Atom| parent(X, X)].patternMatch [Atom| parent(xerces, brooke)]
#eval [Atom| parent(X, X)].patternMatch [Atom| parent(xerces, xerces)]

def Rule.getSubs (rule : Rule) (db : List Atom) : List SubstitutionC :=
  rule.body.foldl (fun subs pattern =>
    subs.flatMap (fun sub =>
      db.filterMap (fun target =>
        pattern.patternMatch target sub
      )
    )
  ) [[]]

def Program.step (prog : Program) (db : List Atom) : List Atom :=
  db.append (prog.flatMap (fun rule =>
    rule.getSubs db |>.map (fun sub =>
      Atom.applySubC sub rule.head
    )
  ))

def Program.eval (prog : Program) (db : List Atom := []) : Finset Atom :=
  let db' := prog.step db
  if db'.toFinset = db.toFinset then db.toFinset else prog.eval db'
  termination_by
    (prog.hb \ db.toFinset).card
  decreasing_by
    sorry

#eval! Program.eval [Prog|
parent(xerces, brooke).
parent(brooke, damocles).
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
]
