import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

variable [EnoughInjectives C] (n : ℤ)

variable (hf : ∀ i < n, QuasiIsoAt f i)

omit [EnoughInjectives C] in
theorem quasiIso_truncGEπ [Mono f] [Mono (homologyMap f n)] :
    QuasiIso ((cokernel f).πTruncGE n) := by
  rw [quasiIso_πTruncGE_iff]
  exact CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.isGE_cokernel f n hf

attribute [local instance] HasDerivedCategory.standard in

