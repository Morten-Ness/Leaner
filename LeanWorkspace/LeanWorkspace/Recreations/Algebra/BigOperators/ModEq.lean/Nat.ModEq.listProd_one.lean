import Mathlib

variable {α : Type*} {n : ℕ} {l : List α} {f g : α → ℕ}

theorem listProd_one {l : List ℕ} (h : ∀ x ∈ l, x ≡ 1 [MOD n]) : l.prod ≡ 1 [MOD n] := by
  simpa using Nat.ModEq.listProd_map_one h

