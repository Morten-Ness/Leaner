FAIL
import Mathlib

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

variable (S' : Subalgebra R S)

theorem mem_of_span_eq_top_of_smul_pow_mem
    (s : Set S) (l : s →₀ S) (hs : Finsupp.linearCombination S ((↑) : s → S) l = 1)
    (hs' : s ⊆ S') (hl : ∀ i, l i ∈ S') (x : S) (H : ∀ r : s, ∃ n : ℕ, (r : S) ^ n • x ∈ S') :
    x ∈ S' := by
  have hsx : Finsupp.linearCombination S ((↑) : s → S) l * x ∈ S' := by
    classical
    rw [Finsupp.linearCombination_apply]
    rw [Finset.sum_mul]
    refine Finset.sum_mem ?_
    intro a ha
    have hla : l a ∈ S' := hl a
    rcases H a with ⟨n, hn⟩
    have hax : (a : S) ^ n * x ∈ S' := by
      simpa [smul_eq_mul] using hn
    have hterm : l a * ((a : S) ^ n * x) ∈ S' := S'.mul_mem hla hax
    simpa [Algebra.smul_def, smul_eq_mul, mul_assoc] using hterm
  have h1x : (1 : S) * x ∈ S' := by simpa [hs] using hsx
  simpa using h1x
