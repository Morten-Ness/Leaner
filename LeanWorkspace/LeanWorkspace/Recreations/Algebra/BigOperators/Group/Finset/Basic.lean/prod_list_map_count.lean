import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_list_map_count [DecidableEq ι] (l : List ι) (f : ι → M) :
    (l.map f).prod = ∏ m ∈ l.toFinset, f m ^ l.count m := by
  induction l with
  | nil => simp only [map_nil, prod_nil, count_nil, pow_zero, prod_const_one]
  | cons a s IH =>
  simp only [List.map, List.prod_cons, toFinset_cons, IH]
  by_cases has : a ∈ s.toFinset
  · rw [insert_eq_of_mem has, ← insert_erase has, Finset.prod_insert (notMem_erase _ _),
      Finset.prod_insert (notMem_erase _ _), ← mul_assoc, count_cons_self, pow_succ']
    congr 1
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [count_cons_of_ne (ne_of_mem_erase hx).symm]
  rw [Finset.prod_insert has, count_cons_self, count_eq_zero_of_not_mem (mt mem_toFinset.2 has), pow_one]
  grind [Finset.prod_congr]

