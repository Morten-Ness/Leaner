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

theorem nonUnitalAlgHom_ext' [DistribMulAction k A] {φ₁ φ₂ : SkewMonoidAlgebra k G →ₙₐ[k] A}
    (h : φ₁.toMulHom.comp (SkewMonoidAlgebra.of k G).toMulHom = φ₂.toMulHom.comp (SkewMonoidAlgebra.of k G).toMulHom) : φ₁ = φ₂ := SkewMonoidAlgebra.nonUnitalAlgHom_ext <| DFunLike.congr_fun h

