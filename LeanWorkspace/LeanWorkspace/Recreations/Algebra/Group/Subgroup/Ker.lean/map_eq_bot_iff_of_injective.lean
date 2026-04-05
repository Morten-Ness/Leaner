import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

theorem map_eq_bot_iff_of_injective {f : G →* N} (hf : Function.Injective f) :
    H.map f = ⊥ ↔ H = ⊥ := by rw [Subgroup.map_eq_bot_iff, MonoidHom.ker_eq_bot_iff f.mpr hf, le_bot_iff]

