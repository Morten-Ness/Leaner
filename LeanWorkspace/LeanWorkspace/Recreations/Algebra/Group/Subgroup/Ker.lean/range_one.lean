import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem range_one : (1 : G →* N).range = ⊥ := SetLike.ext fun x => by simpa using @comm _ (· = ·) _ 1 x

