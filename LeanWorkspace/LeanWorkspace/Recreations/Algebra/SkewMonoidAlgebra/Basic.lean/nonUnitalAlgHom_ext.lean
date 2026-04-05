import Mathlib

variable {k G : Type*}

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]

variable {A : Type*} [NonUnitalNonAssocSemiring A] [Monoid G] [Semiring k] [MulSemiringAction G k]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem nonUnitalAlgHom_ext [DistribMulAction k A] {φ₁ φ₂ : SkewMonoidAlgebra k G →ₙₐ[k] A}
    (h : ∀ x, φ₁ (SkewMonoidAlgebra.single x 1) = φ₂ (SkewMonoidAlgebra.single x 1)) : φ₁ = φ₂ := by
  apply NonUnitalAlgHom.to_distribMulActionHom_injective
  apply SkewMonoidAlgebra.distribMulActionHom_ext'
  intro a
  ext
  simp [singleAddHom_apply, h]

