import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem Normal.comap {H : Subgroup N} (hH : H.Normal) (f : G →* N) : (H.comap f).Normal :=
  hH.comap f
