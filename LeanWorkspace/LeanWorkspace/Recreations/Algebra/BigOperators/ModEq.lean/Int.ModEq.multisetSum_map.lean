import Mathlib

variable {α : Type*} {n : ℤ} {l : List α} {f g : α → ℤ}

theorem multisetSum_map {s : Multiset α} (h : ∀ x ∈ s, f x ≡ g x [ZMOD n]) :
    Nat.ModEq.sum (s.map f) ≡ Nat.ModEq.sum (s.map g) [ZMOD n] := by
  rcases s with ⟨l⟩
  simpa using Int.ModEq.listSum_map (l := l) h

