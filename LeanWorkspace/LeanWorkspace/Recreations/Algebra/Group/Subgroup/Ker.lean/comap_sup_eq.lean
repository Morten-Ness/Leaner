import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem comap_sup_eq (H K : Subgroup N) (hf : Function.Surjective f) :
    comap f H ⊔ comap f K = comap f (H ⊔ K) := Subgroup.comap_sup_eq_of_le_range f (MonoidHom.range_eq_top.2 hf ▸ le_top) (MonoidHom.range_eq_top.2 hf ▸ le_top)

