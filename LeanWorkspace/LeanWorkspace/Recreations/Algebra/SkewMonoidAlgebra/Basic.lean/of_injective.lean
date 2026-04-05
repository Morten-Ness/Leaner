import Mathlib

variable {k G : Type*}

variable [Semiring k]

variable [Monoid G] [MulSemiringAction G k]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem of_injective [Nontrivial k] :
    Function.Injective (SkewMonoidAlgebra.of k G) := fun a b h ↦ by
  simp_rw [SkewMonoidAlgebra.of_apply, ← SkewMonoidAlgebra.toFinsupp_inj] at h
  simpa using (Finsupp.single_eq_single_iff _ _ _ _).mp h

