import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n₀ n₁ : ℤ)

set_option backward.isDefEq.respectTransparency false in
theorem δ_pOpcycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.δ f g n₀ n₁ hn₁ ≫ X.pOpcycles f g n₁ = 0 := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  simp [CategoryTheory.Abelian.SpectralObject.pOpcycles]

