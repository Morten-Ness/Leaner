import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem coeff_mul_add_eq_of_natDegree_le {df dg : ℕ} {f g : R[X]}
    (hdf : natDegree f ≤ df) (hdg : natDegree g ≤ dg) :
    (f * g).coeff (df + dg) = f.coeff df * g.coeff dg := by
  rw [coeff_mul, Finset.sum_eq_single_of_mem (df, dg)]
  · rw [mem_antidiagonal]
  rintro ⟨df', dg'⟩ hmem hne
  obtain h | hdf' := lt_or_ge df df'
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hdf.trans_lt h), zero_mul]
  obtain h | hdg' := lt_or_ge dg dg'
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hdg.trans_lt h), mul_zero]
  obtain ⟨rfl, rfl⟩ :=
    (add_eq_add_iff_eq_and_eq hdf' hdg').mp (mem_antidiagonal.1 hmem)
  exact (hne rfl).elim

