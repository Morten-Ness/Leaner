import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem comap_normalClosure (s : Set N) (f : G ≃* N) :
    Subgroup.normalClosure (f ⁻¹' s) = (Subgroup.normalClosure s).comap f := by
  have := f.toEquiv.image_symm_eq_preimage s
  simp_all [comap_equiv_eq_map_symm, Subgroup.map_normalClosure s (f.symm : N →* G) f.symm.surjective]

