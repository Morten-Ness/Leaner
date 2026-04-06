import Mathlib

variable {ι M M₀ : Type*}

theorem prod_ne_zero_of_prime [CommMonoidWithZero M₀] [NoZeroDivisors M₀] [Nontrivial M₀]
    (s : Multiset M₀) (h : ∀ x ∈ s, Prime x) : s.prod ≠ 0 := by
  classical
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | @cons a s ih =>
      have ha : Prime a := h a (by simp)
      have hs : ∀ x ∈ s, Prime x := by
        intro x hx
        exact h x (by simp [hx])
      intro hprod
      rw [Multiset.prod_cons] at hprod
      exact (ha.ne_zero <| eq_zero_or_eq_zero_of_mul_eq_zero hprod |>.elim id (fun hs0 => False.elim (ih hs hs0)))
