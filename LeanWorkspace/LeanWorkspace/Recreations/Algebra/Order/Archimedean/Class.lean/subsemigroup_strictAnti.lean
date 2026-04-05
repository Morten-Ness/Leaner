import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem subsemigroup_strictAnti : StrictAnti (MulArchimedeanClass.subsemigroup (M := M)) := by
  intro s t hst
  rw [← SetLike.coe_ssubset_coe]
  refine Set.ssubset_iff_subset_ne.mpr ⟨fun _ h ↦ hst.le h, ?_⟩
  contrapose! hst with heq
  apply le_of_eq
  simpa [MulArchimedeanClass.mk_surjective, MulArchimedeanClass.subsemigroup] using heq

