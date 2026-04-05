import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_one_eq_bot : K.map (1 : G →* N) = ⊥ := eq_bot_iff.mpr <| by
    rintro x ⟨y, _, rfl⟩
    simp

