import Mathlib

variable {α : Type*} {n : ℕ} {l : List α} {f g : α → ℕ}

theorem multisetProd_map_one {s : Multiset α} (h : ∀ x ∈ s, f x ≡ 1 [MOD n]) :
    (s.map f).prod ≡ 1 [MOD n] := by
  simpa using Nat.ModEq.multisetProd_map h

