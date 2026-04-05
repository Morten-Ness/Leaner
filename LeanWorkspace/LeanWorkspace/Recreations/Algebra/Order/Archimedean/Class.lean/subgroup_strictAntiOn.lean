import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable {s : UpperSet (MulArchimedeanClass M)}

theorem subgroup_strictAntiOn : StrictAntiOn (MulArchimedeanClass.subgroup (M := M)) (Set.Iio ⊤) := by
  intro s hs t ht hst
  rw [← SetLike.coe_ssubset_coe]
  rw [← MulArchimedeanClass.subsemigroup_eq_subgroup_of_ne_top (Set.mem_Iio.mp hs).ne_top]
  rw [← MulArchimedeanClass.subsemigroup_eq_subgroup_of_ne_top (Set.mem_Iio.mp ht).ne_top]
  refine Set.ssubset_iff_subset_ne.mpr ⟨by simpa [MulArchimedeanClass.subsemigroup] using hst.le, ?_⟩
  contrapose! hst with heq
  apply le_of_eq
  simpa [MulArchimedeanClass.mk_surjective, MulArchimedeanClass.subsemigroup] using heq

