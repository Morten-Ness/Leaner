import Mathlib

variable {α : Type*} {n : ℕ} {l : List α} {f g : α → ℕ}

theorem listSum_map_zero (h : ∀ x ∈ l, f x ≡ 0 [MOD n]) : (l.map f).sum ≡ 0 [MOD n] := by
  simpa using Nat.ModEq.listSum_map h

