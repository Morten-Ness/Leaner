FAIL
import Mathlib

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_map_eq_pow_single [DecidableEq ι] (i : ι)
    (hf : ∀ i' ≠ i, i' ∈ m → f i' = 1) : (m.map f).prod = f i ^ m.count i := by
  classical
  revert hf
  induction m using Multiset.induction_on with
  | empty =>
      intro hf
      simp
  | @cons a m ih =>
      intro hf
      by_cases h : a = i
      · subst h
        have hfm : ∀ i' ≠ i, i' ∈ m → f i' = 1 := by
          intro i' hi' hm
          exact hf i' hi' (Multiset.mem_cons_of_mem hm)
        rw [Multiset.map_cons, Multiset.prod_cons, ih hfm, Multiset.count_cons, if_pos rfl]
        simp [pow_succ, mul_comm]
      · have hfa : f a = 1 := hf a h (by simp)
        have hfm : ∀ i' ≠ i, i' ∈ m → f i' = 1 := by
          intro i' hi' hm
          exact hf i' hi' (Multiset.mem_cons_of_mem hm)
        rw [Multiset.map_cons, Multiset.prod_cons, hfa, one_mul, ih hfm, Multiset.count_cons, if_neg (Ne.symm h)]
        rfl
