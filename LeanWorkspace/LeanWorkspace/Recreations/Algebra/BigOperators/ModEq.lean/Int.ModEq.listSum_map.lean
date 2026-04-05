import Mathlib

variable {α : Type*} {n : ℤ} {l : List α} {f g : α → ℤ}

theorem listSum_map (h : ∀ x ∈ l, f x ≡ g x [ZMOD n]) : Nat.ModEq.sum (l.map f) ≡ Nat.ModEq.sum (l.map g) [ZMOD n] := by
  induction l <;> aesop (add unsafe Int.ModEq.add)

