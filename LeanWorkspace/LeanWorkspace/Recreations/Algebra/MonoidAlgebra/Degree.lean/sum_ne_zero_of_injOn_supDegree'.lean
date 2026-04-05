import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

variable {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) {f : ι → R[A]}

variable [AddZeroClass A]

theorem sum_ne_zero_of_injOn_supDegree' (hs : ∃ i ∈ s, f i ≠ 0)
    (hd : (s : Set ι).InjOn (supDegree D ∘ f)) :
    ∑ i ∈ s, f i ≠ 0 := by
  obtain ⟨j, hj, hne⟩ := hs
  obtain ⟨i, hi, he⟩ := exists_mem_eq_sup _ ⟨j, hj⟩ (supDegree D ∘ f)
  by_cases! h : ∀ k ∈ s, k = i
  · refine (sum_eq_single_of_mem j hj (fun k hk hne => ?_)).trans_ne hne
    rw [h k hk, h j hj] at hne; exact hne.irrefl.elim
  obtain ⟨j, hj, hne⟩ := h
  apply AddMonoidAlgebra.ne_zero_of_supDegree_ne_bot (D := D)
  have (k) (hk : k ∈ s) (hne : k ≠ i) : supDegree D (f k) < supDegree D (f i) :=
    ((le_sup hk).trans_eq he).lt_of_ne (hd.ne hk hi hne)
  rw [(AddMonoidAlgebra.supDegree_leadingCoeff_sum_eq hi this).1]
  exact (this j hj hne).ne_bot

