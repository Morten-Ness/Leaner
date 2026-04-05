import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ n₂ : ℤ)

theorem kernelSequenceOpcyclesE_exact (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.kernelSequenceOpcyclesE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).Exact :=
  ShortComplex.exact_of_iso (X.kernelSequenceOpcyclesEIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).symm
    (ShortComplex.exact_of_f_is_kernel _ (ShortComplex.homologyIsKernel _))

