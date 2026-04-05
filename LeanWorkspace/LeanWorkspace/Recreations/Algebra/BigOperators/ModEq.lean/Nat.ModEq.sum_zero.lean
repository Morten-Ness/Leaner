import Mathlib

variable {α : Type*} {n : ℕ} {l : List α} {f g : α → ℕ}

theorem sum_zero {s : Finset α} (h : ∀ x ∈ s, f x ≡ 0 [MOD n]) : ∑ x ∈ s, f x ≡ 0 [MOD n] := by
  simpa using Nat.ModEq.sum h

