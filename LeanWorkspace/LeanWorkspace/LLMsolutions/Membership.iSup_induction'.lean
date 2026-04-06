import Mathlib

variable {M A B : Type*}

variable [MulOneClass M]

theorem iSup_induction' {ι : Sort*} (S : ι → Submonoid M) {motive : ∀ x, (x ∈ ⨆ i, S i) → Prop}
    (mem : ∀ (i), ∀ (x) (hxS : x ∈ S i), motive x (Submonoid.mem_iSup_of_mem i hxS))
    (one : motive 1 (one_mem _))
    (mul : ∀ x y hx hy, motive x hx → motive y hy → motive (x * y) (mul_mem ‹_› ‹_›)) {x : M}
    (hx : x ∈ ⨆ i, S i) : motive x hx := by
  let T : Submonoid M :=
    { carrier := {x | ∃ hx : x ∈ ⨆ i, S i, motive x hx}
      one_mem' := ⟨one_mem _, one⟩
      mul_mem' := by
        rintro a b ⟨ha, hma⟩ ⟨hb, hmb⟩
        refine ⟨mul_mem ha hb, ?_⟩
        exact mul a b ha hb hma hmb }
  have hle : ∀ i, S i ≤ T := by
    intro i x hxS
    exact ⟨Submonoid.mem_iSup_of_mem i hxS, mem i x hxS⟩
  have hxT : x ∈ T := by
    exact (iSup_le hle) hx
  exact hxT.choose_spec
