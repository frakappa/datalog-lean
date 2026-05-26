def List.product (xs : List α) (len : Nat := 1) : List (List α) :=
  match len with
  | 0 => [[]]
  | n + 1 => xs.product n |>.flatMap (fun tup => xs.map (fun x => x :: tup))

#eval [1, 2, 3].product 0
#eval [1, 2, 3].product
#eval [1, 2, 3].product 3

theorem List.mem_product_iff (xs : List α) (len : Nat) :
    ∀ tup, tup ∈ xs.product len ↔ tup.length = len ∧ ∀ e ∈ tup, e ∈ xs := by
  intro tup
  induction len generalizing tup with
  | zero =>
    simp [List.product]
    grind
  | succ n ih =>
    constructor <;> intro h
    · simp [List.product] at h
      grind
    · simp [List.product]
      cases tup with grind
