import Mathlib

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

variable (B : BilinForm R M)

theorem LinearMap.BilinForm.isSkewAdjoint_bracket {f g : Module.End R M}
    (hf : f ∈ B.skewAdjointSubmodule) (hg : g ∈ B.skewAdjointSubmodule) :
    ⁅f, g⁆ ∈ B.skewAdjointSubmodule := by
  rw [mem_skewAdjointSubmodule] at *
  have hfg : IsAdjointPair B B (f * g) (g * f) := by rw [← neg_mul_neg g f]; exact hg.comp hf
  have hgf : IsAdjointPair B B (g * f) (f * g) := by rw [← neg_mul_neg f g]; exact hf.comp hg
  change IsAdjointPair B B (f * g - g * f) (-(f * g - g * f)); rw [neg_sub]
  exact hfg.sub hgf

