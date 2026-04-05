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
  refine Exists.elim ?_ fun (hx : x ∈ ⨆ i, S i) (hc : motive x hx) ↦ hc
  exact Algebra.iSup_induction S (motive := fun x' ↦ ∃ h, motive x' h) mem
    (fun _ _ h ↦ ⟨_, basic _ _ h⟩) (fun _ _ h h' ↦ ⟨_, add _ _ _ _ h.2 h'.2⟩)
    (fun _ _ h h' ↦ ⟨_, mul _ _ _ _ h.2 h'.2⟩) fun _ ↦ ⟨_, algebraMap _⟩

