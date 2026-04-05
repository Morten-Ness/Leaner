import Mathlib

variable {K : Type*} {v : K} {n : ℕ} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

theorem exists_int_eq_of_partDen {b : K}
    (nth_partDen_eq : (of v).partDens.get? n = some b) : ∃ z : ℤ, b = (z : K) := by
  obtain ⟨gp, nth_s_eq, gp_b_eq_b_n⟩ : ∃ gp, (of v).s.get? n = some gp ∧ gp.b = b :=
    exists_s_b_of_partDen nth_partDen_eq
  have : ∃ z : ℤ, gp.b = (z : K) := (GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq nth_s_eq).right
  rwa [gp_b_eq_b_n] at this

