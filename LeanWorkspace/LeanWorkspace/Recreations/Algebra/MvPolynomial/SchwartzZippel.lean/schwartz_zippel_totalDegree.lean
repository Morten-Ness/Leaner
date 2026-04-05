import Mathlib

variable {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]

theorem schwartz_zippel_totalDegree {n} {p : MvPolynomial (Fin n) R} (hp : p ≠ 0) (S : Finset R) :
    #{f ∈ piFinset fun _ ↦ S | eval f p = 0} / (#S ^ n : ℚ≥0) ≤ p.totalDegree / #S := calc
    _ = #{f ∈ piFinset fun _ ↦ S | eval f p = 0} / (∏ i : Fin n, #S : ℚ≥0) := by simp
    _ ≤ p.support.sup fun s ↦ ∑ i, (s i / #S : ℚ≥0) := MvPolynomial.schwartz_zippel_sup_sum hp _
    _ = p.totalDegree / #S := by
      obtain rfl | hs := S.eq_empty_or_nonempty
      · simp
        simp only [← _root_.bot_eq_zero, sup_bot]
      simp_rw [totalDegree, Nat.cast_finsetSup]
      rw [sup_div₀ (by positivity)]
      simp [← sum_div, Finsupp.sum_fintype]

