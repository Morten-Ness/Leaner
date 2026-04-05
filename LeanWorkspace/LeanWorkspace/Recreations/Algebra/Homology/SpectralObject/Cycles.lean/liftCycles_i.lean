import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n₀ n₁ : ℤ)

variable (hn₁ : n₀ + 1 = n₁) {A : C} (x : A ⟶ (X.H n₀).obj (mk₁ g))
    (hx : x ≫ X.δ f g n₀ n₁ hn₁ = 0)

theorem liftCycles_i : X.liftCycles f g n₀ n₁ hn₁ x hx ≫ X.iCycles f g n₀ = x := by
  apply kernel.lift_ι

