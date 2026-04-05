import Mathlib

variable {α : Type*} {n : ℤ} {l : List α} {f g : α → ℤ}

theorem sum {s : Finset α} (h : ∀ x ∈ s, f x ≡ g x [ZMOD n]) :
    (∑ x ∈ s, f x) ≡ ∑ x ∈ s, g x [ZMOD n] := .multisetSum_map (s := s.1) h

