import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem mulArchimedean_of_mk_eq_mk (h : ∀ a ≠ (1 : M), ∀ b ≠ 1, MulArchimedeanClass.mk a = MulArchimedeanClass.mk b) :
    MulArchimedean M where
  arch x y hy := by
    by_cases! hx : x ≤ 1
    · use 0
      simpa using hx
    · have hxy : MulArchimedeanClass.mk x = MulArchimedeanClass.mk y := h x hx.ne.symm y hy.ne.symm
      obtain ⟨_, ⟨m, hm⟩⟩ := MulArchimedeanClass.mk_eq_mk.mp hxy
      rw [mabs_eq_self.mpr hx.le, mabs_eq_self.mpr hy.le] at hm
      exact ⟨m, hm⟩

