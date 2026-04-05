import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n₀ n₁ : ℤ)

set_option backward.isDefEq.respectTransparency false in
theorem iCycles_δ (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.iCycles f g n₀ ≫ X.δ f g n₀ n₁ hn₁ = 0 := by
  subst hn₁
  simp [CategoryTheory.Abelian.SpectralObject.iCycles]

