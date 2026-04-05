import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem star_left_conjugate_nonneg {a : R} (ha : 0 ≤ a) (c : R) : 0 ≤ star c * a * c := by
  rw [StarOrderedRing.nonneg_iff] at ha
  refine AddSubmonoid.closure_induction (fun x hx => ?_)
    (by rw [mul_zero, zero_mul]) (fun x y _ _ hx hy => ?_) ha
  · obtain ⟨x, rfl⟩ := hx
    convert star_mul_self_nonneg (x * c) using 1
    rw [star_mul, ← mul_assoc, mul_assoc _ _ c]
  · calc
      0 ≤ star c * x * c + 0 := by rw [add_zero]; exact hx
      _ ≤ star c * x * c + star c * y * c := by gcongr
      _ ≤ _ := by rw [mul_add, add_mul]

