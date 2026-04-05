import Mathlib

variable {α : Type*} {n : ℤ} {l : List α} {f g : α → ℤ}

theorem listSum_map_zero (h : ∀ x ∈ l, f x ≡ 0 [ZMOD n]) : Nat.ModEq.sum (l.map f) ≡ 0 [ZMOD n] := by
  simpa using Int.ModEq.listSum_map h

