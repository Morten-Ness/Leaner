import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (f : G →* N)

theorem comap_normalizer_eq_of_surjective (H : Subgroup G) {f : N →* G}
    (hf : Function.Surjective f) : (normalizer H).comap f = normalizer (H.comap f) := Subgroup.comap_normalizer_eq_of_le_range fun x _ ↦ hf x

