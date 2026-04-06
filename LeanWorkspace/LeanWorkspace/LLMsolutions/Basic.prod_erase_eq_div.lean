FAIL
import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommGroup G] [DecidableEq ι] {f : ι → G}

theorem prod_erase_eq_div {a : ι} (h : a ∈ s) : ∏ x ∈ s.erase a, f x = (∏ x ∈ s, f x) / f a := by
  calc
    ∏ x ∈ s.erase a, f x = (∏ x ∈ s.erase a, f x) * (f a)⁻¹ := by
      simp
    _ = ((∏ x ∈ s.erase a, f x) * f a) / f a := by
      simp [div_eq_mul_inv, mul_assoc]
    _ = (∏ x ∈ s, f x) / f a := by
      rw [Finset.mul_prod_erase _ _ h]
