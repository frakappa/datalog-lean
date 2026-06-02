import Datalog.Utils

-- Term

inductive Term where
  | const : String → Term
  | var : String → Term
  deriving BEq

instance : ToString Term where
  toString
    | .const c => c
    | .var v => v

def Term.isConst : Term → Bool
  | .const _ => true
  | _ => false

def Term.isVar : Term → Bool
  | .var _ => true
  | _ => false

def Term.isGround : Term → Bool :=
  Term.isConst

-- Atom

structure Atom where
  rel : String
  terms : List Term
  deriving BEq

instance : ToString Atom where
  toString
    | Atom.mk rel [] => rel
    | Atom.mk rel terms => rel ++ "(" ++ ", ".intercalate (terms.map toString) ++ ")"

def Atom.predicate (atom : Atom) : String × Nat :=
  (atom.rel, atom.terms.length)

def Atom.getConstants (atom : Atom) : List Term :=
  atom.terms.filter Term.isConst

def Atom.isGround (atom : Atom) : Bool :=
  ∀ t ∈ atom.terms, t.isGround

-- Rule

structure Rule where
  head : Atom
  body : List Atom
  deriving BEq

instance : ToString Rule where
  toString
    | Rule.mk head [] => toString head ++ "."
    | Rule.mk head body => toString head ++ " :- " ++ ", ".intercalate (body.map toString) ++ "."

def Rule.getPredicates (rule : Rule) : List (String × Nat) :=
  rule.head.predicate :: rule.body.map Atom.predicate

def Rule.getConstants (rule : Rule) : List Term :=
  rule.head.getConstants ++ rule.body.flatMap Atom.getConstants

def Rule.isGround (rule : Rule) : Bool :=
  rule.head.isGround ∧ ∀ a ∈ rule.body, a.isGround

def Rule.isFact (rule : Rule) : Bool :=
  rule.body.isEmpty

-- Program

abbrev Program :=
  List Rule

instance : ToString Program where
  toString prog :=
    "\n".intercalate (prog.map toString)

def Program.getPredicates (prog : Program) : List (String × Nat) :=
  prog.flatMap Rule.getPredicates

def Program.getConstants (prog : Program) : List Term :=
  prog.flatMap Rule.getConstants

def Program.getHerbrandBase (prog : Program) : List Atom :=
  prog.getPredicates.flatMap (fun (rel, arity) => prog.getConstants.product arity |>.map (fun terms => Atom.mk rel terms))
