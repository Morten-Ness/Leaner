FAIL
import Mathlib

variable {α β : Type*} [Neg α]

variable {α β : Type*} [AddCommGroup β] [IsAddTorsionFree β] {f : α → β}

theorem Odd.sum_eq_zero [Fintype α] [InvolutiveNeg α] {f : α → β} (hf : f.Odd) : ∑ a, f a = 0 := by
  classical
  let e : α ≃ α :=
    { toFun := fun a => -a
      invFun := fun a => -a
      left_inv := by intro a; simp
      right_inv := by intro a; simp }
  have hneg : ∑ a, f (-a) = ∑ a, f a := by
    simpa [e] using Fintype.sum_bijective e f
  have hodd : ∑ a, f (-a) = -∑ a, f a := by
    rw [show (∑ a, f (-a)) = ∑ a, (-f a) by
      refine Finset.sum_congr rfl ?_
      intro a ha
      exact hf a]
    rw [Finset.sum_neg_distrib]
  have hadd : ∑ a, f a + ∑ a, f a = 0 := by
    calc
      ∑ a, f a + ∑ a, f a = ∑ a, f a + ∑ a, f (-a) := by rw [hneg.symm]
      _ = 0 := by rw [hodd]; abel
  exact eq_zero_of_two_eq_zero hadd
