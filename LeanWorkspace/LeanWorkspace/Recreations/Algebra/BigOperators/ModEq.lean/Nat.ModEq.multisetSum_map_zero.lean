import Mathlib

variable {α : Type*} {n : ℕ} {l : List α} {f g : α → ℕ}

theorem multisetSum_map_zero {s : Multiset α} (h : ∀ x ∈ s, f x ≡ 0 [MOD n]) :
    (s.map f).sum ≡ 0 [MOD n] := by
  simpa using Nat.ModEq.multisetSum_map h

