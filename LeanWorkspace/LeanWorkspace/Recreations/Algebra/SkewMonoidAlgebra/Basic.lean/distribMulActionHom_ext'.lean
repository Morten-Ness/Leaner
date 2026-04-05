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

theorem distribMulActionHom_ext' [DistribMulAction R M] [DistribMulAction R N] {α : Type*}
    {f g : SkewMonoidAlgebra M α →+[R] N}
    (h : ∀ a : α, f.comp (SkewMonoidAlgebra.DistribMulActionHom.single a) = g.comp (SkewMonoidAlgebra.DistribMulActionHom.single a)) :
    f = g := SkewMonoidAlgebra.distribMulActionHom_ext fun a ↦ DistribMulActionHom.congr_fun (h a)

