import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem disjoint_map {f : G →* N} (hf : Function.Injective f) {H K : Subgroup G} (h : Disjoint H K) :
    Disjoint (H.map f) (K.map f) := by
  rw [Subgroup.disjoint_def] at h ⊢
  intro x hxH hxK
  rcases hxH with ⟨y, hy, rfl⟩
  rcases hxK with ⟨z, hz, hz_eq⟩
  have hyz : y = z := hf hz_eq.symm
  subst hyz
  simpa using congrArg f (h hy hz)
