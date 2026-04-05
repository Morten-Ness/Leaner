import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {H K : Subgroup G}

variable {N : Type*} [Group N]

theorem le_normalizer_comap (f : N →* G) :
    (normalizer H).comap f ≤ normalizer (H.comap f) := fun x => by
  simp only [mem_normalizer_iff, mem_comap]
  intro h n
  simp [h (f n)]

