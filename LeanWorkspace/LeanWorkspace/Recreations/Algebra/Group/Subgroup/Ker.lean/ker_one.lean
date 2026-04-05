import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [MulOneClass M]

theorem ker_one : (1 : G →* M).ker = ⊤ := SetLike.ext fun _x => eq_self_iff_true _

