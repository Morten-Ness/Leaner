import Mathlib

variable {α : Type*} {n : ℤ} {l : List α} {f g : α → ℤ}

theorem multisetProd_one {s : Multiset ℤ} (h : ∀ x ∈ s, x ≡ 1 [ZMOD n]) : Nat.ModEq.prod s ≡ 1 [ZMOD n] := by
  simpa using Int.ModEq.multisetProd_map_one h

