import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem Monic.irreducible_iff_degree_lt (p_monic : Monic p) (p_1 : p ≠ 1) :
    Irreducible p ↔ ∀ q, degree q ≤ ↑(p.natDegree / 2) → q ∣ p → IsUnit q := by
  simp only [p_monic.irreducible_iff_lt_natDegree_lt p_1, Finset.mem_Ioc, and_imp,
    natDegree_pos_iff_degree_pos, natDegree_le_iff_degree_le]
  constructor
  · rintro h q deg_le dvd
    by_contra q_unit
    have := degree_pos_of_not_isUnit_of_dvd_monic p_monic q_unit dvd
    have hu := p_monic.isUnit_leadingCoeff_of_dvd dvd
    refine (h _ (monic_of_isUnit_leadingCoeff_inv_smul hu) ?_ ?_ (dvd_trans ?_ dvd)).elim
    · rwa [degree_smul_of_smul_regular _ (isSMulRegular_of_group _)]
    · rwa [degree_smul_of_smul_regular _ (isSMulRegular_of_group _)]
    · rw [Units.smul_def, Polynomial.smul_eq_C_mul, (isUnit_C.mpr (Units.isUnit _)).mul_left_dvd]
  · rintro h q _ deg_pos deg_le dvd
    exact deg_pos.ne' <| degree_eq_zero_of_isUnit (h q deg_le dvd)

