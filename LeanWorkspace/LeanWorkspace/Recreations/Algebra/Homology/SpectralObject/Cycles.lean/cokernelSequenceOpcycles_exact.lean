import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n₀ n₁ : ℤ)

theorem cokernelSequenceOpcycles_exact (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.cokernelSequenceOpcycles f g n₀ n₁ hn₁).Exact := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  apply ShortComplex.exact_cokernel

