import Mathlib

variable {α : Type*} {n : ℤ} {l : List α} {f g : α → ℤ}

theorem multisetSum_map_zero {s : Multiset α} (h : ∀ x ∈ s, f x ≡ 0 [ZMOD n]) :
    Nat.ModEq.sum (s.map f) ≡ 0 [ZMOD n] := by
  simpa using Int.ModEq.multisetSum_map h

