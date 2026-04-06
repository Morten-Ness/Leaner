import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_inf (H K : Subgroup G) (f : G →* N) (hf : Function.Injective f) :
    (H ⊓ K).map f = H.map f ⊓ K.map f := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy.1, rfl⟩, ⟨y, hy.2, rfl⟩⟩
  · intro hx
    rcases hx with ⟨hxH, hxK⟩
    rcases hxH with ⟨y, hyH, hxy⟩
    rcases hxK with ⟨z, hzK, hxz⟩
    have : y = z := hf (hxy.trans hxz.symm)
    subst z
    exact ⟨y, ⟨hyH, hzK⟩, hxy⟩
