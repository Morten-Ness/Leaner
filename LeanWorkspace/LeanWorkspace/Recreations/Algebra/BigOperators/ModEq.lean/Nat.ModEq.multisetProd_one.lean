import Mathlib

variable {α : Type*} {n : ℕ} {l : List α} {f g : α → ℕ}

theorem multisetProd_one {s : Multiset ℕ} (h : ∀ x ∈ s, x ≡ 1 [MOD n]) : s.prod ≡ 1 [MOD n] := by
  simpa using Nat.ModEq.multisetProd_map_one h

