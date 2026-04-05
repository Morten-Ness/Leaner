import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {M N : Type*} [CommGroup M] [CommGroup N]

theorem map_range_powMonoidHom (e : M ≃* N) (n : ℕ) :
    (powMonoidHom (α := M) n).range.map e = (powMonoidHom (α := N) n).range := by
  have H : (e : M →* N).comp (powMonoidHom n) = (powMonoidHom n).comp e := by ext : 1; simp
  rw [MonoidHom.map_range, H, MonoidHom.range_comp, MulEquiv.range_eq_top e, ← MonoidHom.range_eq_map]

