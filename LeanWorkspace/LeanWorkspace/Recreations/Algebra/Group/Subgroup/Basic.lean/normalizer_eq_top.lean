import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {H K : Subgroup G}

theorem normalizer_eq_top [h : H.Normal] : normalizer (H : Set G) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr h

