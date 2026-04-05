import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [Monoid M]

theorem eqLocus_same (f : G →* N) : f.eqLocus f = ⊤ := SetLike.ext fun _ => eq_self_iff_true _

