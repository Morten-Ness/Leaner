import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem closure_preimage_eq_top (s : Set G) : closure ((closure s).subtype ⁻¹' s) = ⊤ := by
  simp

