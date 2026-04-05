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

theorem distribMulActionHom_ext [DistribMulAction R M] [DistribMulAction R N] {α : Type*}
    {f g : SkewMonoidAlgebra M α →+[R] N}
    (h : ∀ (a : α) (m : M), f (SkewMonoidAlgebra.single a m) = g (SkewMonoidAlgebra.single a m)) : f = g := DistribMulActionHom.toAddMonoidHom_injective <| SkewMonoidAlgebra.addHom_ext h

