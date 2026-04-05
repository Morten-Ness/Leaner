import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable {s : UpperSet (MulArchimedeanClass M)}

theorem subgroup_antitone : Antitone (MulArchimedeanClass.subgroup (M := M)) := by
  intro s t hst
  obtain rfl | hs := eq_or_ne s ⊤
  · rw [eq_top_iff.mpr hst]
  obtain rfl | ht := eq_or_ne t ⊤
  · simp
  rwa [MulArchimedeanClass.subgroup_strictAntiOn.le_iff_ge ht.lt_top hs.lt_top]

