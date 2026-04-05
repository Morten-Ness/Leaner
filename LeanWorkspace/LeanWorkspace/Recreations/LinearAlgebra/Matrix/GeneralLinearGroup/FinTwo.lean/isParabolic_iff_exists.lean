import Mathlib

variable {K : Type*} [Field K] {m : Matrix (Fin 2) (Fin 2) K}

theorem isParabolic_iff_exists [NeZero (2 : K)] :
    m.IsParabolic ↔ ∃ a n, m = scalar _ a + n ∧ n ≠ 0 ∧ n ^ 2 = 0 := by
  constructor
  · exact fun hm ↦ ⟨_, _, (add_sub_cancel ..).symm, sub_ne_zero.mpr fun h ↦ hm.1 ⟨_, h.symm⟩,
      hm.sub_eigenvalue_sq_eq_zero⟩
  · rintro ⟨a, n, hm, hn0, hnsq⟩
    constructor
    · refine fun ⟨b, hb⟩ ↦ hn0 ?_
      rw [← sub_eq_iff_eq_add'] at hm
      simpa only [← hm, ← hb, ← map_sub, ← map_pow, ← map_zero (scalar (Fin 2)), scalar_inj,
        sq_eq_zero_iff] using hnsq
    · suffices scalar (Fin 2) (m.discr / 4) = 0 by
        rw [← map_zero (scalar (Fin 2)), scalar_inj, div_eq_zero_iff] at this
        have : (4 : K) ≠ 0 := by simpa [show (4 : K) = 2 ^ 2 by norm_num] using NeZero.ne _
        tauto
      rw [← Matrix.sub_scalar_sq_eq_discr, hm, trace_add, scalar_apply, trace_diagonal]
      simp [mul_div_cancel_left₀ _ (NeZero.ne (2 : K)),
        (Matrix.isNilpotent_trace_of_isNilpotent ⟨2, hnsq⟩).eq_zero, hnsq]

