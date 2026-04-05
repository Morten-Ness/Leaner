import Mathlib

variable {R : Type*} [CommSemiring R]

theorem sum_eq_natDegree_of_mem_support_homogenize (p : R[X]) {s : Fin 2 →₀ ℕ}
    (hs : s ∈ (p.homogenize p.natDegree).support) :
    s 0 + s 1 = p.natDegree := by
  simp [(Polynomial.isHomogeneous_homogenize p).degree_eq_sum_deg_support hs, ← Finsupp.degree_apply,
        Finsupp.degree_eq_sum]

