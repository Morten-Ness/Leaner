import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem iSup_induction' {ι : Sort*} (S : ι → Subalgebra R A) {motive : ∀ x, (x ∈ ⨆ i, S i) → Prop}
    {x : A} (mem : x ∈ ⨆ i, S i)
    (basic : ∀ (i) (x) (hx : x ∈ S i), motive x (Algebra.mem_iSup_of_mem i hx))
    (add : ∀ x y hx hy, motive x hx → motive y hy → motive (x + y) (add_mem ‹_› ‹_›))
    (mul : ∀ x y hx hy, motive x hx → motive y hy → motive (x * y) (mul_mem ‹_› ‹_›))
    (algebraMap : ∀ r, motive (algebraMap R A r) (Subalgebra.algebraMap_mem (⨆ i, S i) ‹_›)) :
    motive x mem := by
  let P : Subalgebra R A := {
    carrier := {x | ∃ hx : x ∈ ⨆ i, S i, motive x hx}
    algebraMap_mem' := by
      intro r
      exact ⟨Subalgebra.algebraMap_mem (⨆ i, S i) r, algebraMap r⟩
    mul_mem' := by
      intro x y hx hy
      rcases hx with ⟨hx, hmx⟩
      rcases hy with ⟨hy, hmy⟩
      exact ⟨mul_mem hx hy, mul x y hx hy hmx hmy⟩
    add_mem' := by
      intro x y hx hy
      rcases hx with ⟨hx, hmx⟩
      rcases hy with ⟨hy, hmy⟩
      exact ⟨add_mem hx hy, add x y hx hy hmx hmy⟩
    zero_mem' := by
      simpa using (algebraMap (0 : R))
    one_mem' := by
      simpa using (algebraMap (1 : R)) }
  have h_le : ∀ i, S i ≤ P := by
    intro i x hx
    exact ⟨Algebra.mem_iSup_of_mem i hx, basic i x hx⟩
  have hxP : x ∈ P := by
    exact show x ∈ P from (iSup_le h_le) mem
  exact hxP.choose_spec
