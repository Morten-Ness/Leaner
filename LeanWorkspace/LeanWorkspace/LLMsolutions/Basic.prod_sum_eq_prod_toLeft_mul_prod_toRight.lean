FAIL
import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_sum_eq_prod_toLeft_mul_prod_toRight (s : Finset (ι ⊕ κ)) (f : ι ⊕ κ → M) :
    ∏ x ∈ s, f x = (∏ x ∈ s.toLeft, f (Sum.inl x)) * ∏ x ∈ s.toRight, f (Sum.inr x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert x s hx ih =>
      rcases x with x | x
      · simp [hx, ih]
      · simp [hx, ih, mul_left_comm, mul_assoc]
