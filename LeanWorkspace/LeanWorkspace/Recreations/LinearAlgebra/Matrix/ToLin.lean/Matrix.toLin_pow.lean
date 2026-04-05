import Mathlib

variable {R : Type*} [CommSemiring R]

variable {l m n : Type*} [Fintype n] [DecidableEq n]

variable {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]

variable (v₁ : Basis n R M₁) (v₂ : Basis m R M₂)

variable [Fintype m]

variable {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃] (v₃ : Basis l R M₃)

theorem Matrix.toLin_pow (A : Matrix n n R) (k : ℕ) :
    (A ^ k).toLin v₁ v₁ = (A.toLin v₁ v₁) ^ k := by
  induction k with
  | zero => simp only [pow_zero, toLin_one, End.one_eq_id]
  | succ n ih => rw [pow_succ, pow_succ, toLin_mul v₁ v₁, ih, Module.End.mul_eq_comp]

