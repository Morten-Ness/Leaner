import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem closure_induction₂ {s : Set R} {p : (x y : R) → x ∈ Subsemiring.closure s → y ∈ Subsemiring.closure s → Prop}
    (mem_mem : ∀ (x) (y) (hx : x ∈ s) (hy : y ∈ s), p x y (Subsemiring.subset_closure hx) (Subsemiring.subset_closure hy))
    (zero_left : ∀ x hx, p 0 x (zero_mem _) hx) (zero_right : ∀ x hx, p x 0 hx (zero_mem _))
    (one_left : ∀ x hx, p 1 x (one_mem _) hx) (one_right : ∀ x hx, p x 1 hx (one_mem _))
    (add_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x + y) z (add_mem hx hy) hz)
    (add_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y + z) hx (add_mem hy hz))
    (mul_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x * y) z (mul_mem hx hy) hz)
    (mul_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y * z) hx (mul_mem hy hz))
    {x y : R} (hx : x ∈ Subsemiring.closure s) (hy : y ∈ Subsemiring.closure s) :
    p x y hx hy := by
  induction hy using Subsemiring.closure_induction with
  | mem z hz => induction hx using Subsemiring.closure_induction with
    | mem _ h => exact mem_mem _ _ h hz
    | zero => exact zero_left _ _
    | one => exact one_left _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
  | zero => exact zero_right x hx
  | one => exact one_right x hx
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | add _ _ _ _ h₁ h₂ => exact add_right _ _ _ _ _ _ h₁ h₂

