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
    { carrier := {a : A | motive a}
      algebraMap_mem' := algebraMap
      mul_mem' := by
        intro a b ha hb
        exact mul a b ha hb
      add_mem' := by
        intro a b ha hb
        exact add a b ha hb
      zero_mem' := by simpa using algebraMap 0
      one_mem' := by simpa using algebraMap 1 }
  have hle : ∀ i, S i ≤ T := by
    intro i a ha
    exact basic i a ha
  have hs : (⨆ i, S i) ≤ T := iSup_le hle
  exact hs mem
