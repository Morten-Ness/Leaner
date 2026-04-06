FAIL
import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_multiset_map_count [DecidableEq ι] (s : Multiset ι) {M : Type*} [CommMonoid M]
    (f : ι → M) : (s.map f).prod = ∏ m ∈ s.toFinset, f m ^ s.count m := by
  classical
  refine Multiset.induction_on s ?_ ?_
  · simp
  · intro a s ih
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.toFinset_cons]
    by_cases h : a ∈ s.toFinset
    · rw [Finset.prod_insert (Finset.not_mem_erase _ _)]
      · rw [show insert a s.toFinset = s.toFinset by exact Finset.insert_eq_of_mem h]
        rw [← ih]
        have hcount : Multiset.count a (a ::ₘ s) = Multiset.count a s + 1 := by
          simp
        have hmap :
            (f a) * (s.map f).prod =
              (s.map f).prod * f a := by
          simp [mul_comm]
        rw [hmap]
        congr 1
        simp [hcount, pow_succ, mul_comm, mul_left_comm, mul_assoc]
      · simp
    · rw [Finset.prod_insert h]
      rw [ih]
      simp [h, pow_succ, mul_comm, mul_left_comm, mul_assoc]
