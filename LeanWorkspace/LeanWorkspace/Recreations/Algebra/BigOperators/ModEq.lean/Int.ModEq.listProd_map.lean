import Mathlib

variable {α : Type*} {n : ℤ} {l : List α} {f g : α → ℤ}

theorem listProd_map (h : ∀ x ∈ l, f x ≡ g x [ZMOD n]) :
    Nat.ModEq.prod (l.map f) ≡ Nat.ModEq.prod (l.map g) [ZMOD n] := by
  induction l <;> aesop (add unsafe Int.ModEq.mul)

