import Mathlib

variable {α : Type*} {n : ℤ} {l : List α} {f g : α → ℤ}

theorem multisetProd_map {s : Multiset α} (h : ∀ x ∈ s, f x ≡ g x [ZMOD n]) :
    Nat.ModEq.prod (s.map f) ≡ Nat.ModEq.prod (s.map g) [ZMOD n] := by
  rcases s with ⟨l⟩
  simpa using Int.ModEq.listProd_map (l := l) h

