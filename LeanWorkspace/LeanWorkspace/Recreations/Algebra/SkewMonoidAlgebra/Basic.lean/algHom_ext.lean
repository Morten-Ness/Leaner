import Mathlib

variable {k G : Type*}

variable [Monoid G] [CommSemiring k]

variable {A : Type*} [Semiring A] [Algebra k A]

variable [MulSemiringAction G k] [SMulCommClass G k k]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem algHom_ext ⦃φ₁ φ₂ : AlgHom k (SkewMonoidAlgebra k G) A⦄
    (h : ∀ x, φ₁ (SkewMonoidAlgebra.single x 1) = φ₂ (SkewMonoidAlgebra.single x 1)) : φ₁ = φ₂ := AlgHom.toLinearMap_injective (SkewMonoidAlgebra.lhom_ext' fun a ↦ (LinearMap.ext_ring (h a)))

