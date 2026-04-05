import Mathlib

variable {k G : Type*}

variable {S S₁ S₂ : Type*}

variable {M α : Type*} [Monoid G] [AddCommMonoid M] [MulAction G α]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem comapSMul_def (g : G) (f : SkewMonoidAlgebra M α) : g • f = SkewMonoidAlgebra.mapDomain (g • ·) f := rfl

