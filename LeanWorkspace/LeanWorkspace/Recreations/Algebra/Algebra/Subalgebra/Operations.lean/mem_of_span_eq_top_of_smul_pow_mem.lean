import Mathlib

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

variable (S' : Subalgebra R S)

theorem mem_of_span_eq_top_of_smul_pow_mem
    (s : Set S) (l : s →₀ S) (hs : Finsupp.linearCombination S ((↑) : s → S) l = 1)
    (hs' : s ⊆ S') (hl : ∀ i, l i ∈ S') (x : S) (H : ∀ r : s, ∃ n : ℕ, (r : S) ^ n • x ∈ S') :
    x ∈ S' := Subalgebra.mem_of_finset_sum_eq_one_of_pow_smul_mem S' l.support (↑) l hs (fun x => hs' x.2) hl x H

