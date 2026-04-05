import Mathlib

variable {k G : Type*}

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem lhom_ext {α : Type*} [Module R M] [Module R N] ⦃φ ψ : SkewMonoidAlgebra M α →ₗ[R] N⦄
    (h : ∀ a b, φ (SkewMonoidAlgebra.single a b) = ψ (SkewMonoidAlgebra.single a b)) : φ = ψ := LinearMap.toAddMonoidHom_injective <| SkewMonoidAlgebra.addHom_ext h

