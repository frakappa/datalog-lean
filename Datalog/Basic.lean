inductive Term where
  | const : String → Term
  | var : String → Term

instance : ToString Term where
  toString
    | .const s | .var s => s

structure Atom where
  rel : String
  terms : List Term

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

#eval ([
  .mk (.mk "parent" [.const "xerces", .const "brooke"]) [],
  .mk (.mk "parent" [.const "brooke", .const "damocles"]) [],
  .mk (.mk "ancestor" [.var "X", .var "Y"]) [.mk "parent" [.var "X", .var "Y"]],
  .mk (.mk "ancestor" [.var "X", .var "Y"]) [.mk "parent" [.var "X", .var "Z"], .mk "ancestor" [.var "Z", .var "Y"]],
] : Program)
