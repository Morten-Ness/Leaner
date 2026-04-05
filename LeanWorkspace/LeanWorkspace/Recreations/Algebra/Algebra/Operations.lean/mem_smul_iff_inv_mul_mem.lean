import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem mem_smul_iff_inv_mul_mem {S} [DivisionSemiring S] [Algebra R S] {x : S} {p : Submodule R S}
    {y : S} (hx : x ≠ 0) : y ∈ x • p ↔ x⁻¹ * y ∈ p := by
  constructor
  · rintro ⟨a, ha : a ∈ p, rfl⟩; simpa [inv_mul_cancel_left₀ hx]
  · exact fun h ↦ ⟨_, h, by simp [mul_inv_cancel_left₀ hx]⟩

