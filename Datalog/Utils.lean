def List.product (xs : List α) (len : Nat := 1) : List (List α) :=
  match len with
  | 0 => [[]]
  | n + 1 => xs.product n |>.flatMap (fun p => xs.map (fun x => x :: p))

#eval [1, 2, 3].product
#eval [1, 2, 3].product 3
