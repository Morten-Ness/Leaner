import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem mk_eq_mk_of_mulArchimedean [MulArchimedean M] (ha : a ≠ 1) (hb : b ≠ 1) :
    MulArchimedeanClass.mk a = MulArchimedeanClass.mk b := by
  obtain hm := MulArchimedean.arch |b|ₘ (show 1 < |a|ₘ by simpa using ha)
  obtain hn := MulArchimedean.arch |a|ₘ (show 1 < |b|ₘ by simpa using hb)
  exact MulArchimedeanClass.mk_eq_mk.mpr ⟨hm, hn⟩

