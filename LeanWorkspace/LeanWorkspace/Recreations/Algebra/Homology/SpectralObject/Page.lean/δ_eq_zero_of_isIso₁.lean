import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)

theorem δ_eq_zero_of_isIso₁ (hf : IsIso f) (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.δ f g n₀ n₁ hn₁ = 0 := by
  simpa only [Preadditive.IsIso.comp_left_eq_zero] using X.zero₃ f g _ rfl n₀ n₁

