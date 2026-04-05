import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem star_left_conjugate_le_conjugate {a b : R} (hab : a ≤ b) (c : R) :
    star c * a * c ≤ star c * b * c := by
  rw [StarOrderedRing.le_iff] at hab ⊢
  obtain ⟨p, hp, rfl⟩ := hab
  simp_rw [← StarOrderedRing.nonneg_iff] at hp ⊢
  exact ⟨star c * p * c, star_left_conjugate_nonneg hp c, by simp only [add_mul, mul_add]⟩

