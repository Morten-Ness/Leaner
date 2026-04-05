import Mathlib

variable {α : Type*} {n : ℕ} {l : List α} {f g : α → ℕ}

theorem prod {s : Finset α} (h : ∀ x ∈ s, f x ≡ g x [MOD n]) :
    (∏ x ∈ s, f x) ≡ ∏ x ∈ s, g x [MOD n] := .multisetProd_map (s := s.1) h

