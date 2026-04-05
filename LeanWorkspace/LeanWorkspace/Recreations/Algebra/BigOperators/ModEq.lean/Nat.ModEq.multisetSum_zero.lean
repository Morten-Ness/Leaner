import Mathlib

variable {α : Type*} {n : ℕ} {l : List α} {f g : α → ℕ}

theorem multisetSum_zero {s : Multiset ℕ} (h : ∀ x ∈ s, x ≡ 0 [MOD n]) : s.sum ≡ 0 [MOD n] := by
  simpa using Nat.ModEq.multisetSum_map h

