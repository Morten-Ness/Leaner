import Mathlib

variable {M N G H α β γ δ : Type*}

theorem IsScalarTower.of_smul_one_mul {M N} [Monoid N] [SMul M N]
    (h : ∀ (x : M) (y : N), x • (1 : N) * y = x • y) : IsScalarTower M N N := ⟨fun x y z ↦ by rw [← h, smul_eq_mul, mul_assoc, h, smul_eq_mul]⟩

