import Mathlib

variable {M A B : Type*}

variable [MulOneClass M]

theorem iSup_induction' {ι : Sort*} (S : ι → Submonoid M) {motive : ∀ x, (x ∈ ⨆ i, S i) → Prop}
    (mem : ∀ (i), ∀ (x) (hxS : x ∈ S i), motive x (Submonoid.mem_iSup_of_mem i hxS))
    (one : motive 1 (one_mem _))
    (mul : ∀ x y hx hy, motive x hx → motive y hy → motive (x * y) (mul_mem ‹_› ‹_›)) {x : M}
    (hx : x ∈ ⨆ i, S i) : motive x hx := by
  refine Exists.elim (?_ : ∃ Hx, motive x Hx) fun (hx : x ∈ ⨆ i, S i) (hc : motive x hx) => hc
  refine @Submonoid.iSup_induction _ _ ι S (fun m => ∃ hm, motive m hm) _ hx (fun i x hx => ?_) ?_
      fun x y => ?_
  · exact ⟨_, mem _ _ hx⟩
  · exact ⟨_, one⟩
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    exact ⟨_, mul _ _ _ _ Cx Cy⟩

