import Mathlib

variable {R : Type u} [CommRing R] {p n : ℕ} [ExpChar R p] {f : R[X]} {r : R}

theorem rootMultiplicity_expand_pow :
    (Polynomial.expand R (p ^ n) f).rootMultiplicity r = p ^ n * f.rootMultiplicity (r ^ p ^ n) := by
  obtain rfl | h0 := eq_or_ne f 0; · simp
  obtain ⟨g, hg, ndvd⟩ := f.exists_eq_pow_rootMultiplicity_mul_and_not_dvd h0 (r ^ p ^ n)
  rw [dvd_iff_isRoot, ← eval_X (x := r), ← eval_pow, ← isRoot_comp, ← Polynomial.expand_eq_comp_X_pow] at ndvd
  conv_lhs => rw [hg, map_mul, map_pow, map_sub, Polynomial.expand_X, Polynomial.expand_C, map_pow, ← sub_pow_expChar_pow,
    ← pow_mul, mul_comm, rootMultiplicity_mul_X_sub_C_pow (Polynomial.expand_ne_zero (expChar_pow_pos R p n)
      |>.mpr <| right_ne_zero_of_mul <| hg ▸ h0), rootMultiplicity_eq_zero ndvd, zero_add]

