import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_inf_eq (H K : Subgroup G) (f : G →* N) (hf : Function.Injective f) :
    Subgroup.map f (H ⊓ K) = Subgroup.map f H ⊓ Subgroup.map f K := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy.1, rfl⟩, ⟨y, hy.2, rfl⟩⟩
  · intro hx
    rcases hx with ⟨hxH, hxK⟩
    rcases hxH with ⟨y, hyH, hyfx⟩
    rcases hxK with ⟨z, hzK, hzfx⟩
    have hyz : y = z := hf (hyfx.trans hzfx.symm)
    subst hyz
    exact ⟨y, ⟨hyH, hzK⟩, hyfx⟩
