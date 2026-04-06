FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [MulOneClass M]

theorem ker_toHomUnits {M} [Monoid M] (f : G →* M) : f.toHomUnits.ker = f.ker := by
  ext x
  constructor
  · intro hx
    change (f x : Units M) = 1 at hx
    exact Units.ext hx
  · intro hx
    change (f x : Units M) = 1
    exact Units.ext hx
