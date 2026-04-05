import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {H K : Subgroup G}

variable {N : Type*} [Group N]

theorem _root_.normalizerCondition_iff_only_full_group_self_normalizing :
    NormalizerCondition G ↔ ∀ H : Subgroup G, normalizer H = H → H = ⊤ := by
  apply forall_congr'; intro H
  simp only [lt_iff_le_and_ne, le_normalizer, Ne]
  tauto

