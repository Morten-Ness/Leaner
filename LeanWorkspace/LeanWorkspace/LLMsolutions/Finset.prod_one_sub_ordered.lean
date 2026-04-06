FAIL
import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [CommRing R]

theorem prod_one_sub_ordered [LinearOrder ι] (s : Finset ι) (f : ι → R) :
    ∏ i ∈ s, (1 - f i) = 1 - ∑ i ∈ s, f i * ∏ j ∈ s with j < i, (1 - f j) := by
  classical
  classical
  induction' s using Finset.induction_on with a s ha hs
  · simp
  · rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hprod_a : ∏ j ∈ insert a s with j < a, (1 - f j) = 1 := by
      rw [Finset.prod_eq_one]
      intro x hx
      simp at hx
    rw [hprod_a, hs]
    have hsum :
        ∑ x ∈ s, f x * ∏ j ∈ insert a s with j < x, (1 - f j)
          = (1 - f a) * ∑ x ∈ s, f x * ∏ j ∈ s with j < x, (1 - f j) := by
      rw [← Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro x hx
      by_cases hax : a < x
      · have hmem : a ∉ s.filter fun j => j < x := by
          intro h
          exact ha ((Finset.mem_filter.mp h).1)
        rw [show ∏ j ∈ insert a s with j < x, (1 - f j)
              = ∏ j in insert a (s.filter fun j => j < x), (1 - f j) by
              simp [Finset.mem_filter]]
        rw [Finset.prod_insert hmem]
        · simp [hax, mul_assoc, mul_left_comm, mul_comm]
        · simp [hax]
      · have hnot : ¬ a < x := hax
        have hfilter :
            (insert a s).filter (fun j => j < x) = s.filter (fun j => j < x) := by
          ext j
          simp [hnot, ha, and_left_comm, and_assoc]
        rw [show ∏ j ∈ insert a s with j < x, (1 - f j)
              = ∏ j ∈ s with j < x, (1 - f j) by
              rw [← Finset.prod_filter]
              rw [← Finset.prod_filter]
              simpa [hfilter]]
        ring
    rw [hsum]
    ring
