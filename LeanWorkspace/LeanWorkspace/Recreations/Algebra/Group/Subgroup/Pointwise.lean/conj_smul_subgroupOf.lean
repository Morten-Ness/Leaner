import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

variable [Group α] [MulDistribMulAction α G]

theorem conj_smul_subgroupOf {P H : Subgroup G} (hP : P ≤ H) (h : H) :
    MulAut.conj h • P.subgroupOf H = (MulAut.conj (h : G) • P).subgroupOf H := by
  refine le_antisymm ?_ ?_
  · rintro - ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro p ⟨g, hg, hp⟩
    exact ⟨⟨g, hP hg⟩, hg, Subtype.ext hp⟩

