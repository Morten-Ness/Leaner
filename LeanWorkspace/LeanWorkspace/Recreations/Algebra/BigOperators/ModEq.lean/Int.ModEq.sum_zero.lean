import Mathlib

variable {α : Type*} {n : ℤ} {l : List α} {f g : α → ℤ}

theorem sum_zero {s : Finset α} (h : ∀ x ∈ s, f x ≡ 0 [ZMOD n]) :
    (∑ x ∈ s, f x) ≡ 0 [ZMOD n] := .multisetSum_map_zero (s := s.1) h

