import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

variable [EnoughInjectives C] (n : ℤ)

theorem quasiIsoAt_π (q : ℤ) (hq : q < n) : QuasiIsoAt (π f n) q := by
  have := CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.mono_homologyMap_π f n q (by lia)
  have := CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.epi_homologyMap_π f n q hq
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply Balanced.isIso_of_mono_of_epi

