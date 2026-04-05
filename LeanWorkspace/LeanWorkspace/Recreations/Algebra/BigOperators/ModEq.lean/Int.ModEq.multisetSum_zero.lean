import Mathlib

variable {α : Type*} {n : ℤ} {l : List α} {f g : α → ℤ}

theorem multisetSum_zero {s : Multiset ℤ} (h : ∀ x ∈ s, x ≡ 0 [ZMOD n]) : Nat.ModEq.sum s ≡ 0 [ZMOD n] := by
  simpa using Int.ModEq.multisetSum_map_zero h

