import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem mk_inv (a : M) : MulArchimedeanClass.mk a⁻¹ = MulArchimedeanClass.mk a := MulArchimedeanClass.mk_eq_mk.mpr ⟨⟨1, by simp⟩, ⟨1, by simp⟩⟩

