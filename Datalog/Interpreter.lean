import Datalog.DSL
import Datalog.Spec

abbrev SubstitutionC :=
  List (String × String)

def SubstitutionC.toFun (sub : SubstitutionC) : String → String :=
  fun v => sub.lookup v |>.getD ""

def Atom.patternMatch (pattern target : Atom) (sub : SubstitutionC := []) : Option SubstitutionC := do
  guard (pattern.predicate == target.predicate)
  let mut sub := sub
  for (a₁, a₂) in pattern.terms.zip target.terms do
    match a₁, a₂ with
    | .const c₁, .const c₂ => guard (c₁ == c₂)
    | .var v, .const c =>
      match sub.lookup v with
      | some c' => guard (c == c')
      | none => sub := (v, c) :: sub
    | _, _ => none
  some sub

#eval [Atom| parent(X, Y)].patternMatch [Atom| parent(xerces, brooke)]
#eval [Atom| parent(X, Y)].patternMatch [Atom| ancestor(xerces, brooke)]
#eval [Atom| parent(X, Y)].patternMatch [Atom| parent(xerces, brooke, damocles)]
#eval [Atom| parent(X, X)].patternMatch [Atom| parent(xerces, brooke)]
#eval [Atom| parent(X, X)].patternMatch [Atom| parent(xerces, xerces)]

def Term.applySubC (sub : SubstitutionC) : Term → Term
  | .const c => .const c
  | .var v => .const (sub.lookup v |>.getD "")

def Atom.applySubC (sub : SubstitutionC) (atom : Atom) : Atom :=
  Atom.mk atom.rel (atom.terms.map (Term.applySubC sub))

theorem Term.applySubC_eq_applySub_toFun (term : Term) (sub : SubstitutionC) : term.applySubC sub = term.applySub sub.toFun := by
  simp [Term.applySubC, Term.applySub, SubstitutionC.toFun]
  rfl

theorem Atom.applySubC_eq_applySub_toFun (atom : Atom) (sub : SubstitutionC) : atom.applySubC sub = atom.applySub sub.toFun := by
  simp [Atom.applySubC, Atom.applySub]
  intro t ht
  exact Term.applySubC_eq_applySub_toFun t sub

#eval [Atom| parent(X, Y)].applySubC [("Y", "brooke"), ("X", "xerces")]
#eval [Atom| parent(X, X)].applySubC [("X", "xerces")]

def Rule.getSubs (rule : Rule) (db : List Atom) : List SubstitutionC :=
  rule.body.foldl (fun subs pattern => subs.flatMap (fun sub => db.filterMap (fun target => pattern.patternMatch target sub))) [[]]

def Program.step (prog : Program) (db : List Atom) : List Atom :=
  prog.flatMap (fun rule => rule.getSubs db |>.map (fun sub => Atom.applySubC sub rule.head))

def toFun (db : List Atom) : Atom → Prop :=
  fun a => a ∈ db

partial def Program.eval (prog : Program) (db : List Atom := []) : List Atom :=
  let db' := prog.step db
  if db' == db then db else prog.eval db'

#eval Program.eval [Prog|
parent(xerces, brooke).
parent(brooke, damocles).
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
]
