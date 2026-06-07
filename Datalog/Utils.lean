import Mathlib.Tactic

def Finset.cartesianPower {α : Type} [DecidableEq (List α)] (s : Finset α) (len : Nat) : Finset (List α) :=
  match len with
  | 0 => {[]}
  | n + 1 => s.cartesianPower n |>.biUnion (fun tup => s.image (· :: tup))

#eval ({1, 2, 3} : Finset Nat).cartesianPower 0
#eval ({1, 2, 3} : Finset Nat).cartesianPower 1
#eval ({1, 2, 3} : Finset Nat).cartesianPower 3

theorem Finset.mem_cartesianPower {α : Type} [DecidableEq (List α)] {s : Finset α} {len : Nat} {tup : List α} :
    tup ∈ s.cartesianPower len ↔ tup.length = len ∧ ∀ e ∈ tup, e ∈ s := by
  induction len generalizing tup with
  | zero => grind [Finset.cartesianPower]
  | succ n ih => cases tup with grind [Finset.cartesianPower]
