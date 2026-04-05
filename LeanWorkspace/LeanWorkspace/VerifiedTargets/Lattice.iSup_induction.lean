import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem iSup_induction {ι : Sort*} (S : ι → Subalgebra R A) {motive : A → Prop}
    {x : A} (mem : x ∈ ⨆ i, S i)
    (basic : ∀ i, ∀ a ∈ S i, motive a)
    (add : ∀ a b, motive a → motive b → motive (a + b))
    (mul : ∀ a b, motive a → motive b → motive (a * b))
    (algebraMap : ∀ r, motive (algebraMap R A r)) : motive x := by
  let T : Subalgebra R A :=
  { carrier := {x | motive x}
    mul_mem' {a b} := mul a b
    add_mem' {a b} := add a b
    algebraMap_mem' := algebraMap }
  suffices iSup S ≤ T from this mem
  rwa [iSup_le_iff]

