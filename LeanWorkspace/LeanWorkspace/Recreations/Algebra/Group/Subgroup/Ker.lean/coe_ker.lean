import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [MulOneClass M]

theorem coe_ker (f : G →* M) : (f.ker : Set G) = (f : G → M) ⁻¹' {1} := rfl

