import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (n₀ n₁ n₂ : ℤ)

theorem isZero_E_of_isZero_H (h : IsZero ((X.H n₁).obj (mk₁ f₂)))
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsZero (X.E f₁ f₂ f₃ n₀ n₁ n₂) :=
  (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).exact_iff_isZero_homology.1
    (ShortComplex.exact_of_isZero_X₂ _ h)

