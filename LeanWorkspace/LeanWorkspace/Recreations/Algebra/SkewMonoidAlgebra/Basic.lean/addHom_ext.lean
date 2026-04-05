import Mathlib

variable {k G : Type*}

variable [AddCommMonoid k]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem addHom_ext {M : Type*} [AddZeroClass M] {f g : SkewMonoidAlgebra k G →+ M}
    (h : ∀ a b, f (SkewMonoidAlgebra.single a b) = g (SkewMonoidAlgebra.single a b)) : f = g := by
  ext p; induction p using SkewMonoidAlgebra.induction_on <;> simp_all

