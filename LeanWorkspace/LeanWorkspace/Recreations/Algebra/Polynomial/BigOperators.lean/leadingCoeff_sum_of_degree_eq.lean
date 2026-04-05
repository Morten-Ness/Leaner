import Mathlib

open scoped Polynomial

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable {S : Type*} [Semiring S]

theorem leadingCoeff_sum_of_degree_eq {f : ι → S[X]} {s : Finset ι} {d}
    (hd : ∀ k ∈ s, (f k).degree = d) (hf : ∑ k ∈ s, (f k).leadingCoeff ≠ 0) :
    (∑ k ∈ s, f k).leadingCoeff = ∑ k ∈ s, (f k).leadingCoeff := by
  obtain _ | d := d
  · simp_all [WithBot.none_eq_bot]
  · replace hd k (hk : k ∈ s) : (f k).natDegree = d := natDegree_eq_of_degree_eq_some <| hd k hk
    suffices (∑ k ∈ s, f k).natDegree = d by simp_all [leadingCoeff]
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · aesop (add safe Polynomial.natDegree_sum_le_of_forall_le)
    · simp_all [leadingCoeff]

