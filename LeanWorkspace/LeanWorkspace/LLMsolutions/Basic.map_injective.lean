import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem map_injective {f : A →ₐ[R] B} (hf : Function.Injective f) : Function.Injective (Subalgebra.map f) := by
  intro S₁ S₂ h
  ext x
  constructor
  · intro hx
    have hmem : f x ∈ Subalgebra.map f S₁ := ⟨x, hx, rfl⟩
    rw [h] at hmem
    rcases hmem with ⟨y, hy, hxy⟩
    exact hf hxy ▸ hy
  · intro hx
    have hmem : f x ∈ Subalgebra.map f S₂ := ⟨x, hx, rfl⟩
    rw [← h] at hmem
    rcases hmem with ⟨y, hy, hxy⟩
    exact hf hxy ▸ hy
