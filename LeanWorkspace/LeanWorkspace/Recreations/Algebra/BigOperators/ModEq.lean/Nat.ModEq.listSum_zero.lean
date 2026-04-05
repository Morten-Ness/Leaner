import Mathlib

variable {α : Type*} {n : ℕ} {l : List α} {f g : α → ℕ}

theorem listSum_zero {l : List ℕ} (h : ∀ x ∈ l, x ≡ 0 [MOD n]) : l.sum ≡ 0 [MOD n] := by
  simpa using Nat.ModEq.listSum_map h

