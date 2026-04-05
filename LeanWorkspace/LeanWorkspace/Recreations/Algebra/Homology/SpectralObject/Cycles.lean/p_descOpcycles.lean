import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n₀ n₁ : ℤ)

variable (hn₁ : n₀ + 1 = n₁) {A : C} (x : (X.H n₁).obj (mk₁ f) ⟶ A)
    (hx : X.δ f g n₀ n₁ hn₁ ≫ x = 0)

theorem p_descOpcycles : X.pOpcycles f g n₁ ≫ X.descOpcycles f g n₀ n₁ hn₁ x hx = x := by
  apply cokernel.π_desc

