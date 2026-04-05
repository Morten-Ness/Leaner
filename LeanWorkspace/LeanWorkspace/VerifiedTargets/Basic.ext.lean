import Mathlib

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)

variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]

variable [Module k V] [Module k V₂] [Module k V₃]

variable [AddTorsor V P] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃]

variable {P P₂ P₃}

variable {k}

theorem ext {n : ℕ} {s1 s2 : Affine.Simplex k P n} (h : ∀ i, s1.points i = s2.points i) : s1 = s2 := by
  cases s1
  cases s2
  congr with i
  exact h i

