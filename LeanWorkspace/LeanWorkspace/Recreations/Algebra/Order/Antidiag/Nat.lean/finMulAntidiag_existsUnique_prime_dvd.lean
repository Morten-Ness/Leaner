import Mathlib

open scoped ArithmeticFunction

theorem finMulAntidiag_existsUnique_prime_dvd {d n p : ℕ} (hn : Squarefree n)
    (hp : p ∈ n.primeFactorsList) (f : Fin d → ℕ) (hf : f ∈ Nat.finMulAntidiag d n) :
    ∃! i, p ∣ f i := by
  rw [Nat.mem_finMulAntidiag] at hf
  rw [mem_primeFactorsList hf.2, ← hf.1, hp.1.prime.dvd_finset_prod_iff] at hp
  obtain ⟨i, his, hi⟩ := hp.2
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hij
  apply Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp.1, hi, hj⟩
  apply Nat.coprime_of_squarefree_mul
  apply hn.squarefree_of_dvd
  rw [← hf.1, ← Finset.mul_prod_erase _ _ his,
    ← Finset.mul_prod_erase _ _ (mem_erase.mpr ⟨hij, Finset.mem_univ _⟩), ← mul_assoc]
  apply Nat.dvd_mul_right

