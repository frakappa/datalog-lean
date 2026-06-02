def List.product {α : Type} (xs : List α) (len : Nat) : List (List α) :=
  match len with
  | 0 => [[]]
  | n + 1 => xs.product n |>.flatMap (fun tup => xs.map (fun x => x :: tup))

#eval [1, 2, 3].product 0
#eval [1, 2, 3].product 1
#eval [1, 2, 3].product 3

theorem List.mem_product_iff {α : Type} (xs : List α) (len : Nat) (tup : List α) :
    tup ∈ xs.product len ↔ tup.length = len ∧ ∀ e ∈ tup, e ∈ xs := by
  induction len generalizing tup with
  | zero => grind [List.product]
  | succ n ih => cases tup with grind [List.product]
