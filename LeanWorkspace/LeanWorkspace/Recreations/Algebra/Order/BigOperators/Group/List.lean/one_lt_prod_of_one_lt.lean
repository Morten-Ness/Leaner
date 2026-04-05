import Mathlib

variable {ι α M N : Type*}

theorem one_lt_prod_of_one_lt [CommMonoid M] [Preorder M] [IsOrderedMonoid M] :
    ∀ l : List M, (∀ x ∈ l, (1 : M) < x) → l ≠ [] → 1 < l.prod
  | [], _, h => (h rfl).elim
  | [b], h, _ => by simpa using h
  | a :: b :: l, hl₁, _ => by
    simp only [forall_eq_or_imp, List.mem_cons] at hl₁
    rw [List.prod_cons]
    apply one_lt_mul_of_lt_of_le' hl₁.1
    apply le_of_lt ((b :: l).one_lt_prod_of_one_lt _ (l.cons_ne_nil b))
    grind
