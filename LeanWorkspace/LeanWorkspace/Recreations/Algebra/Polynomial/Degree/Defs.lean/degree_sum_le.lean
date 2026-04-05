import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem degree_sum_le (s : Finset ι) (f : ι → R[X]) :
    Polynomial.degree (∑ i ∈ s, f i) ≤ s.sup fun b => Polynomial.degree (f b) := Finset.cons_induction_on s (by simp)
    fun a s has ih =>
    calc
      Polynomial.degree (∑ i ∈ cons a s has, f i) ≤ max (Polynomial.degree (f a)) (Polynomial.degree (∑ i ∈ s, f i)) := by
        rw [Finset.sum_cons]; exact Polynomial.degree_add_le _ _
      _ ≤ _ := by rw [sup_cons]; exact max_le_max le_rfl ih

