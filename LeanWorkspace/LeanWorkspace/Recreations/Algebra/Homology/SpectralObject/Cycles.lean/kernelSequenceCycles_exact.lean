import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n₀ n₁ : ℤ)

theorem kernelSequenceCycles_exact (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.kernelSequenceCycles f g n₀ n₁ hn₁).Exact := by
  subst hn₁
  apply ShortComplex.exact_kernel

