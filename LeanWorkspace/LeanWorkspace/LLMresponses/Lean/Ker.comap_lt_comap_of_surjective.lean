import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem comap_lt_comap_of_surjective {f : G →* N} {K L : Subgroup N} (hf : Function.Surjective f) :
    K.comap f < L.comap f ↔ K < L := by
  constructor
  · rintro ⟨hKL, hne⟩
    refine ⟨?_, ?_⟩
    · intro x hxK
      rcases hf x with ⟨y, rfl⟩
      exact hKL hxK
    · intro hLK
      apply hne
      intro x hxL
      exact hLK hxL
  · rintro ⟨hKL, hne⟩
    refine ⟨Subgroup.comap_mono hKL, ?_⟩
    intro hEq
    apply hne
    intro x hxL
    rcases hf x with ⟨y, rfl⟩
    exact hEq hxL
