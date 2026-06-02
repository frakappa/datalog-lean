import Datalog.DSL
import Datalog.Utils

-- Substitution

abbrev Substitution :=
  String → String

def Term.applySub (σ : Substitution) : Term → Term
  | .const c => .const c
  | .var v => .const (σ v)

def Atom.applySub (σ : Substitution) (atom : Atom) : Atom :=
  Atom.mk atom.rel (atom.terms.map (Term.applySub σ))

theorem isConst_of_mem_applySub {term : Term} {atom : Atom} {σ : Substitution} (h : term ∈ (atom.applySub σ).terms) :
    term.isConst := by
  simp [Atom.applySub, Term.applySub] at h
  simp [Term.isConst]
  grind

-- Predicates

def Program.Predicates (prog : Program) (pred : String × Nat) : Prop :=
  ∃ r ∈ prog, pred = r.head.predicate ∨ ∃ a ∈ r.body, pred = a.predicate

theorem Program.mem_getPredicates_iff (prog : Program) (pred : String × Nat) :
    pred ∈ prog.getPredicates ↔ prog.Predicates pred := by
  simp [Program.getPredicates, Rule.getPredicates, Atom.predicate, Program.Predicates]
  grind

-- Constants

def Program.Constants (prog : Program) (t : Term) : Prop :=
  t.isConst ∧ ∃ r ∈ prog, t ∈ r.head.terms ∨ ∃ a ∈ r.body, t ∈ a.terms

theorem Program.mem_getConstants_iff (prog : Program) (term : Term) :
    term ∈ prog.getConstants ↔ prog.Constants term := by
  simp [Program.getConstants, Rule.getConstants, Atom.getConstants, Program.Constants]
  grind

-- Herbrand base

def Program.HerbrandBase (prog : Program) (a : Atom) : Prop :=
  prog.Predicates a.predicate ∧ ∀ t ∈ a.terms, prog.Constants t

theorem Program.mem_getHerbrandBase_iff (prog : Program) (atom : Atom) :
    atom ∈ prog.getHerbrandBase ↔ prog.HerbrandBase atom := by
  simp [Program.getHerbrandBase, Program.mem_getPredicates_iff, List.mem_product_iff, Program.mem_getConstants_iff, Program.HerbrandBase, Atom.predicate]
  grind

-- Herbrand model

inductive Program.HerbrandModel (prog : Program) : Atom → Prop where
  | step : {r : Rule} → r ∈ prog → (σ : Substitution) → ({a : Atom} → a ∈ r.body → prog.HerbrandModel (a.applySub σ)) → prog.HerbrandModel (r.head.applySub σ)

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

theorem HerbrandModel_subseteq_HerbrandBase (prog : Program) (safety : prog.IsSafe) (atom : Atom) :
    prog.HerbrandModel atom → prog.HerbrandBase atom := by
  intro h
  induction h with
  | step hr σ hbody ih =>
    rename_i r
    constructor
    · simp [Program.Predicates, Atom.predicate, Atom.applySub]
      grind
    · intro t ht
      constructor
      · exact isConst_of_mem_applySub ht
      · cases Classical.em (t ∈ r.head.terms) with
        | inl hhead => exact ⟨r, hr, .inl hhead⟩
        | inr hhead =>
          have ⟨s, hs⟩ : ∃ s, .var s ∈ r.head.terms ∧ .const (σ s) = t := by
            simp [Atom.applySub, Term.applySub, List.mem_map] at ht
            grind
          have ⟨a, ha⟩ := (safety r hr) (.var s) hs.left (by simp [Term.isVar])
          have : t ∈ (a.applySub σ).terms := by
            simp [Atom.applySub, Term.applySub]
            grind
          simp [Program.HerbrandBase, Program.Constants] at ih
          grind

-- Fixpoint semantics

def Subseteq {α : Type} (s₁ s₂ : α → Prop) : Prop :=
  ∀ e, s₁ e → s₂ e

infix:50 " ⊆ " => Subseteq

def Program.ImmediateConsequence (prog : Program) (db : Atom → Prop) (atom : Atom) : Prop :=
  ∃ r ∈ prog, ∃ σ, r.head.applySub σ = atom ∧ ∀ a ∈ r.body, db (a.applySub σ)

def Program.LeastFixedPoint (prog : Program) (atom : Atom) : Prop :=
  ∀ db, prog.ImmediateConsequence db ⊆ db → db atom

theorem ImmediateConsequence_monotonic (prog : Program) :
    ∀ db₁ db₂, db₁ ⊆ db₂ → prog.ImmediateConsequence db₁ ⊆ prog.ImmediateConsequence db₂ := by
  intro db₁ db₂ h
  simp [Subseteq, Program.ImmediateConsequence]
  intro a r hr σ hσ hbody
  refine ⟨r, hr, σ, hσ, ?_⟩
  simp [Subseteq] at h
  grind

theorem HerbrandModel_iff_LeastFixedPoint (prog : Program) (atom : Atom) :
    prog.HerbrandModel atom ↔ prog.LeastFixedPoint atom := by
  constructor
  · intro h db hdb
    induction h with
    | step hr σ _ ih =>
      apply hdb
      exact ⟨_, hr, σ, rfl, fun _ => ih⟩
  · intro h
    apply h
    intro a ⟨r, hr, σ, hσ, hbody⟩
    rw [← hσ]
    apply Program.HerbrandModel.step hr _ (fun {a} ha => hbody a ha)
