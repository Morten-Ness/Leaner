import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [MulOneClass M]

theorem ker_codRestrict {S} [SetLike S N] [SubmonoidClass S N] (f : G →* N) (s : S)
    (h : ∀ x, f x ∈ s) : (f.codRestrict s h).ker = f.ker := by
  ext x
  constructor
  · intro hx
    exact congrArg Subtype.val hx
  · intro hx
    apply Subtype.ext
    simpa using hx
