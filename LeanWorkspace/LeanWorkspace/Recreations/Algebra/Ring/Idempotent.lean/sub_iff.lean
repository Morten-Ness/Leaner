import Mathlib

variable {R : Type*}

theorem sub_iff [NonUnitalRing R] [IsAddTorsionFree R] {p q : R}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    IsIdempotentElem (q - p) ↔ p * q = p ∧ q * p = p := by
  refine ⟨fun hqp ↦ ?_, fun ⟨h1, h2⟩ => IsIdempotentElem.sub hp hq h1 h2⟩
  have h : p * (q - p) + (q - p) * p = 0 := IsIdempotentElem.add_iff hp hqp |>.mp ((add_sub_cancel p q).symm ▸ hq)
  have hpq : Commute p q := by
    simp_rw [IsIdempotentElem, mul_sub, sub_mul,
    hp.eq, hq.eq, ← sub_add_eq_sub_sub, sub_right_inj, add_sub] at hqp
    have h1 := congr_arg (q * ·) hqp
    have h2 := congr_arg (· * q) hqp
    simp_rw [mul_sub, mul_add, ← mul_assoc, hq.eq, add_sub_cancel_right] at h1
    simp_rw [sub_mul, add_mul, mul_assoc, hq.eq, add_sub_cancel_left, ← mul_assoc] at h2
    exact h2.symm.trans h1
  rw [hpq.eq, and_self, ← nsmul_right_inj (by simp : 2 ≠ 0), ← zero_add (2 • p)]
  convert congrArg (· + 2 • p) h using 1
  simp [sub_mul, mul_sub, hp.eq, hpq.eq, two_nsmul, sub_add, sub_sub]

