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
  prog.flatMap Rule.getPredicates

#eval Program.getPredicates [Program|
parent(xerces, brooke).
parent(brooke, damocles).
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
] |>.eraseDups

def Atom.getConstants (atom : Atom) : List Term :=
  atom.terms.filter Term.isConst

def Rule.getConstants (rule : Rule) : List Term :=
  rule.head.getConstants ++ rule.body.flatMap Atom.getConstants

def Program.getConstants (prog : Program) : List Term :=
  prog.flatMap Rule.getConstants

#eval Program.getConstants [Program|
parent(xerces, brooke).
parent(brooke, damocles).
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
] |>.eraseDups

def Program.getHerbrandBase (prog : Program) : List Atom :=
  prog.getPredicates.flatMap (fun (rel, arity) => prog.getConstants.product arity |>.map (Atom.mk rel ·))

#eval Program.getHerbrandBase [Program|
parent(xerces, brooke).
parent(brooke, damocles).
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
] |>.eraseDups

theorem Program.mem_getPredicates_iff (prog : Program) :
    ∀ p, p ∈ prog.getPredicates ↔ prog.Predicates p := by
  intro p
  simp [Program.getPredicates, Rule.getPredicates, Atom.predicate, Program.Predicates]
  grind

theorem Program.mem_getConstants_iff (prog : Program) :
    ∀ t, t ∈ prog.getConstants ↔ prog.Constants t := by
  intro t
  simp [Program.getConstants, Rule.getConstants, Atom.getConstants, Program.Constants]
  grind

theorem Program.mem_getHerbrandBase_iff (prog : Program) :
    ∀ a, a ∈ prog.getHerbrandBase ↔ prog.HerbrandBase a := by
  intro a
  simp [Program.getHerbrandBase, Program.mem_getPredicates_iff, List.mem_product_iff, Program.mem_getConstants_iff, Program.HerbrandBase, Atom.predicate]
  grind

def Rule.IsSafe (rule : Rule) : Prop :=
  ∀ t ∈ rule.head.terms, t.isVar → ∃ a ∈ rule.body, t ∈ a.terms

def Program.IsSafe (prog : Program) : Prop :=
  ∀ r ∈ prog, r.IsSafe

example : Program.IsSafe [Program|
parent(xerces, brooke).
parent(brooke, damocles).
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
] := by simp [Program.IsSafe, Rule.IsSafe, Term.isVar]

theorem isConst_of_mem_applySub {t : Term} {a : Atom} {σ : Substitution} (h : t ∈ (a.applySub σ).terms) :
    t.isConst := by
  simp [Atom.applySub] at h
  simp [Term.isConst]
  grind

theorem HerbrandModel_subseteq_HerbrandBase (prog : Program) (safety : prog.IsSafe) :
    ∀ a, prog.HerbrandModel a → prog.HerbrandBase a := by
  intro a h
  induction h with
  | step h_r_mem_prog σ HerbrandModel_of_mem_body ih =>
    rename_i r
    simp [Program.HerbrandBase]
    constructor
    · simp [Program.Predicates, Atom.predicate, Atom.applySub]
      grind
    · intro t h_t_mem_applySub
      simp [Program.Constants]
      constructor
      · exact isConst_of_mem_applySub h_t_mem_applySub
      · cases Classical.em (t ∈ r.head.terms) with
        | inl h_t_mem_head => exact ⟨r, h_r_mem_prog, .inl h_t_mem_head⟩
        | inr h_t_not_mem_head =>
          have ⟨s, hs⟩ : ∃ s, .var s ∈ r.head.terms ∧ .const (σ s) = t := by
            simp [Atom.applySub, List.mem_map] at h_t_mem_applySub
            grind
          have ⟨a', ha'⟩ := (safety r h_r_mem_prog) (.var s) hs.left (by simp [Term.isVar])
          have : t ∈ (a'.applySub σ).terms := by
            simp [Atom.applySub]
            grind
          simp [Program.HerbrandBase, Program.Constants] at ih
          grind

def Subseteq (db₁ db₂ : Atom → Prop) : Prop :=
  ∀ a, db₁ a → db₂ a

infix:50 " ⊆ " => Subseteq

def Program.ImmediateConsequence (prog : Program) (db : Atom → Prop) (a : Atom) : Prop :=
  ∃ r ∈ prog, ∃ σ, r.head.applySub σ = a ∧ ∀ a' ∈ r.body, db (a'.applySub σ)

def Program.LeastFixedPoint (prog : Program) (a : Atom) : Prop :=
  ∀ db, prog.ImmediateConsequence db ⊆ db → db a

theorem ImmediateConsequence_monotonic (prog : Program) :
    ∀ db₁ db₂, db₁ ⊆ db₂ → prog.ImmediateConsequence db₁ ⊆ prog.ImmediateConsequence db₂ := by
  intro db₁ db₂ h
  simp [Subseteq, Program.ImmediateConsequence]
  intro a r hr σ hσ ha
  refine ⟨r, hr, σ, hσ, ?_⟩
  simp [Subseteq] at h
  grind

theorem HerbrandModel_iff_LeastFixedPoint (prog : Program) :
    ∀ a, prog.HerbrandModel a ↔ prog.LeastFixedPoint a := by
  intro a
  constructor
  · intro h db hdb
    induction h with
    | step hr σ _ ih =>
      apply hdb
      exact ⟨_, hr, σ, rfl, fun a' => ih⟩
  · intro h
    apply h
    intro a' ⟨r, hr, σ, hσ, hbody⟩
    rw [← hσ]
    apply Program.HerbrandModel.step hr _ (fun {a} ha => hbody a ha)
