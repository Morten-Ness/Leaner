import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem iSup_induction' {ι : Sort*} (S : ι → Subgroup G) {C : ∀ x, (x ∈ ⨆ i, S i) → Prop}
    (hp : ∀ (i), ∀ x (hx : x ∈ S i), C x (mem_iSup_of_mem i hx)) (h1 : C 1 (one_mem _))
    (hmul : ∀ x y hx hy, C x hx → C y hy → C (x * y) (mul_mem ‹_› ‹_›)) {x : G}
    (hx : x ∈ ⨆ i, S i) : C x hx := by
  suffices ∃ h, C x h from this.snd
  refine Subgroup.iSup_induction S (C := fun x => ∃ h, C x h) hx (fun i x hx => ?_) ?_ fun x y => ?_
  · exact ⟨_, hp i _ hx⟩
  · exact ⟨_, h1⟩
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    exact ⟨_, hmul _ _ _ _ Cx Cy⟩

