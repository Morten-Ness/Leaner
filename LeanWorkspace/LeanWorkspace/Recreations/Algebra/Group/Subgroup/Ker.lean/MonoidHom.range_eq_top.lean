import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem range_eq_top {N} [Group N] {f : G →* N} :
    f.range = (⊤ : Subgroup N) ↔ Function.Surjective f := SetLike.ext'_iff.trans <| Iff.trans (by rw [MonoidHom.coe_range, coe_top]) Set.range_eq_univ

