import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem eqOn_adjoin_iff {φ ψ : A →ₐ[R] B} {s : Set A} :
    Set.EqOn φ ψ (Algebra.adjoin R s) ↔ Set.EqOn φ ψ s := by
  have (S : Set A) : S ≤ equalizer φ ψ ↔ Set.EqOn φ ψ S := Iff.rfl
  simp only [← this, Set.le_eq_subset, SetLike.coe_subset_coe, Algebra.adjoin_le_iff]

