FAIL
import Mathlib

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

variable (S' : Subalgebra R S)

theorem mem_of_finset_sum_eq_one_of_pow_smul_mem
    {ι : Type*} (ι' : Finset ι) (s : ι → S) (l : ι → S)
    (e : ∑ i ∈ ι', l i * s i = 1) (hs : ∀ i, s i ∈ S') (hl : ∀ i, l i ∈ S') (x : S)
    (H : ∀ i, ∃ n : ℕ, (s i ^ n : S) • x ∈ S') : x ∈ S' := by
  classical
  have hsum : ∑ i in ι', (l i * s i) • x ∈ S' := by
    refine Finset.sum_mem ?_
    intro i hi
    rcases H i with ⟨n, hn⟩
    cases n with
    | zero =>
        simpa [smul_eq_mul, mul_assoc] using S'.mul_mem (hl i) hn
    | succ n =>
        have hs_pow : s i ^ n ∈ S' := S'.pow_mem (hs i) n
        have hli : l i * s i ^ n ∈ S' := S'.mul_mem (hl i) hs_pow
        have hmul : (l i * s i ^ n) * (s i ^ Nat.succ n • x) ∈ S' := by
          exact S'.mul_mem hli hn
        simpa [smul_eq_mul, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hx : x = ∑ i in ι', (l i * s i) • x := by
    calc
      x = (1 : S) • x := by simp
      _ = (∑ i in ι', l i * s i) • x := by rw [e]
      _ = ∑ i in ι', (l i * s i) • x := by rw [Finset.sum_smul]
  rw [hx]
  exact hsum
