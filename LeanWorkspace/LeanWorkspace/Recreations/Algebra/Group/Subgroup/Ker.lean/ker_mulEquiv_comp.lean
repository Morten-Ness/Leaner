import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [MulOneClass M]

theorem ker_mulEquiv_comp {P : Type*} [MulOneClass P] (f : G →* N) (iso : N ≃* P) :
    ((iso : N →* P).comp f).ker = f.ker := by
  ext
  simp

