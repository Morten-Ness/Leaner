import Mathlib

variable {α : Type*} {n : ℤ} {l : List α} {f g : α → ℤ}

theorem listSum_zero {l : List ℤ} (h : ∀ x ∈ l, x ≡ 0 [ZMOD n]) : Nat.ModEq.sum l ≡ 0 [ZMOD n] := by
  simpa using Int.ModEq.listSum_map_zero h

