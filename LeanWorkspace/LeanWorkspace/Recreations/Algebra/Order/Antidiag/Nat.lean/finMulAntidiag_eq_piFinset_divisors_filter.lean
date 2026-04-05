import Mathlib

open scoped ArithmeticFunction

theorem finMulAntidiag_eq_piFinset_divisors_filter {d m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    Nat.finMulAntidiag d m =
      {f ∈ Fintype.piFinset fun _ : Fin d => n.divisors | ∏ i, f i = m} := by
  ext f
  simp only [ne_eq,
    Fintype.mem_piFinset, mem_divisors, mem_filter]
  constructor
  · intro hf
    refine ⟨?_, Nat.prod_eq_of_mem_finMulAntidiag hf⟩
    exact fun i => ⟨(Nat.dvd_of_mem_finMulAntidiag hf i).trans hmn, hn⟩
  · rw [Nat.mem_finMulAntidiag]
    exact fun ⟨_, hprod⟩ => ⟨hprod, ne_zero_of_dvd_ne_zero hn hmn⟩

