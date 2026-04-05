import Mathlib

variable {R K : Type*} [CommRing R] [Field K]

theorem parabolicEigenvalue_ne_zero {g : GL (Fin 2) K} [NeZero (2 : K)] (hg : Matrix.IsParabolic g) :
    g.val.parabolicEigenvalue ≠ 0 := by
  have : g.val.trace ^ 2 = 4 * g.val.det := by simpa [sub_eq_zero, discr_fin_two] using hg.2
  rw [Matrix.parabolicEigenvalue, div_ne_zero_iff, eq_true_intro (two_ne_zero' K), and_true,
    Ne, ← sq_eq_zero_iff, this, show (4 : K) = 2 ^ 2 by norm_num, mul_eq_zero,
    sq_eq_zero_iff, not_or]
  exact ⟨NeZero.ne _, g.det_ne_zero⟩

