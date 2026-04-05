import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem isMonicOfDegree_iff [Nontrivial R] (p : R[X]) (n : ℕ) :
    IsMonicOfDegree p n ↔ p.natDegree ≤ n ∧ p.coeff n = 1 := by
  simp only [isMonicOfDegree_iff']
  refine ⟨fun ⟨H₁, H₂⟩ ↦ ⟨H₁.le, H₁ ▸ Monic.coeff_natDegree H₂⟩, fun ⟨H₁, H₂⟩ ↦ ⟨?_, ?_⟩⟩
  · exact natDegree_eq_of_le_of_coeff_ne_zero H₁ <| H₂ ▸ one_ne_zero
  · exact monic_of_natDegree_le_of_coeff_eq_one n H₁ H₂

