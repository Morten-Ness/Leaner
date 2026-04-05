import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_iInf {ι : Sort*} [Nonempty ι] (f : G →* N) (hf : Function.Injective f)
    (s : ι → Subgroup G) : (iInf s).map f = ⨅ i, (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

