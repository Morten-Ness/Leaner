import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem closure_induction₂ {p : (x y : M) → x ∈ Subsemigroup.closure s → y ∈ Subsemigroup.closure s → Prop}
    (mem : ∀ (x) (y) (hx : x ∈ s) (hy : y ∈ s), p x y (Subsemigroup.subset_closure hx) (Subsemigroup.subset_closure hy))
    (mul_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x * y) z (mul_mem hx hy) hz)
    (mul_right : ∀ x y z hx hy hz, p z x hz hx → p z y hz hy → p z (x * y) hz (mul_mem hx hy))
    {x y : M} (hx : x ∈ Subsemigroup.closure s) (hy : y ∈ Subsemigroup.closure s) : p x y hx hy := by
  induction hx using Subsemigroup.closure_induction with
  | mem z hz => induction hy using Subsemigroup.closure_induction with
    | mem _ h => exact mem _ _ hz h
    | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ hy h₁ h₂

