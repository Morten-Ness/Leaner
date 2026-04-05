import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [MulOneClass M]

theorem ker_fst : ker (fst G G') = .prod ⊥ ⊤ := SetLike.ext fun _ => (iff_of_eq (and_true _)).symm

