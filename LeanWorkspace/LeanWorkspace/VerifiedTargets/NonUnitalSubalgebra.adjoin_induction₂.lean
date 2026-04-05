import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem adjoin_induction₂ {s : Set A} {p : ∀ x y, x ∈ NonUnitalAlgebra.adjoin R s → y ∈ NonUnitalAlgebra.adjoin R s → Prop}
    (mem_mem : ∀ (x) (y) (hx : x ∈ s) (hy : y ∈ s), p x y (NonUnitalAlgebra.subset_adjoin R hx) (NonUnitalAlgebra.subset_adjoin R hy))
    (zero_left : ∀ x hx, p 0 x (zero_mem _) hx) (zero_right : ∀ x hx, p x 0 hx (zero_mem _))
    (add_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x + y) z (add_mem hx hy) hz)
    (add_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y + z) hx (add_mem hy hz))
    (mul_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x * y) z (mul_mem hx hy) hz)
    (mul_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y * z) hx (mul_mem hy hz))
    (smul_left : ∀ r x y hx hy, p x y hx hy → p (r • x) y (SMulMemClass.smul_mem r hx) hy)
    (smul_right : ∀ r x y hx hy, p x y hx hy → p x (r • y) hx (SMulMemClass.smul_mem r hy))
    {x y : A} (hx : x ∈ NonUnitalAlgebra.adjoin R s) (hy : y ∈ NonUnitalAlgebra.adjoin R s) :
    p x y hx hy := by
  induction hy using NonUnitalAlgebra.adjoin_induction with
  | mem z hz =>
    induction hx using NonUnitalAlgebra.adjoin_induction with
    | mem _ h => exact mem_mem _ _ h hz
    | zero => exact zero_left _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
    | smul _ _ _ h => exact smul_left _ _ _ _ _ h
  | zero => exact zero_right x hx
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | add _ _ _ _ h₁ h₂ => exact add_right _ _ _ _ _ _ h₁ h₂
  | smul _ _ _ h => exact smul_right _ _ _ _ _ h

