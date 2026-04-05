import Mathlib

variable {M N G H α β γ δ : Type*}

theorem SMulCommClass.of_mul_smul_one {M N} [Monoid N] [SMul M N]
    (H : ∀ (x : M) (y : N), y * x • (1 : N) = x • y) : SMulCommClass M N N := ⟨fun x y z ↦ by rw [← H x z, smul_eq_mul, ← H, smul_eq_mul, mul_assoc]⟩

