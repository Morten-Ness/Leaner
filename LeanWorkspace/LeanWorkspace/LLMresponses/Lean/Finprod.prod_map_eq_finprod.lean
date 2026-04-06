FAIL
import Mathlib

variable {α M : Type*} [DecidableEq α] [CommMonoid M]

theorem prod_map_eq_finprod (s : Multiset α) (f : α → M) :
    (s.map f).prod = ∏ᶠ a, f a ^ s.count a := by
  classical
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | @cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, ih]
      have hsplit :
          (∏ᶠ x, f x ^ Multiset.count x (a ::ₘ s)) =
            (f a ^ Multiset.count a (a ::ₘ s)) *
              ∏ᶠ x in {a}ᶜ, f x ^ Multiset.count x (a ::ₘ s) := by
        simpa using (finprod_mem_mul_finprod_mem_compl (s := ({a} : Set α)) (f := fun x => f x ^ Multiset.count x (a ::ₘ s)))
      rw [hsplit]
      have ha_count : Multiset.count a (a ::ₘ s) = Multiset.count a s + 1 := by
        simp
      have hcompl :
          ∏ᶠ x in {a}ᶜ, f x ^ Multiset.count x (a ::ₘ s) =
            ∏ᶠ x in {a}ᶜ, f x ^ Multiset.count x s := by
        refine finprod_mem_congr ?_
        intro x hx
        have hx' : x ≠ a := by
          simpa [Set.mem_compl, Set.mem_singleton_iff] using hx
        simp [Multiset.count_cons, hx', if_neg hx']
      rw [hcompl, ha_count, pow_succ', mul_assoc]
      congr 1
      symm
      have hsplit' :
          (∏ᶠ x, f x ^ Multiset.count x s) =
            (f a ^ Multiset.count a s) *
              ∏ᶠ x in {a}ᶜ, f x ^ Multiset.count x s := by
        simpa using (finprod_mem_mul_finprod_mem_compl (s := ({a} : Set α)) (f := fun x => f x ^ Multiset.count x s))
      rw [hsplit']
      simp
