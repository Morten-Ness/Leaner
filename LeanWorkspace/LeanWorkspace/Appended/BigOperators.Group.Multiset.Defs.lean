import Mathlib

section

variable {F ι M N : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem pow_count [DecidableEq M] (a : M) : a ^ s.count a = (s.filter (Eq a)).prod := by
  rw [filter_eq, Multiset.prod_replicate]

end

section

variable {F ι M N : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_eq_foldl (s : Multiset M) :
    Multiset.prod s = foldl (· * ·) 1 s := (foldr_swap _ _ _).trans (by simp [mul_comm])

end

section

variable {F ι M N : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_hom_rel (s : Multiset ι) {r : M → N → Prop} {f : ι → M} {g : ι → N}
    (h₁ : r 1 1) (h₂ : ∀ ⦃a b c⦄, r b c → r (f a * b) (g a * c)) :
    r (s.map f).prod (s.map g).prod := Quotient.inductionOn s fun l => by
    simp only [l.prod_hom_rel h₁ h₂, quot_mk_to_coe, map_coe, Multiset.prod_coe]

end

section

variable {F ι M N : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_induction (p : M → Prop) (s : Multiset M) (p_mul : ∀ a b, p a → p b → p (a * b))
    (p_one : p 1) (p_s : ∀ a ∈ s, p a) : p s.prod := by
  rw [Multiset.prod_eq_foldr]
  exact foldr_induction (· * ·) 1 p s p_mul p_one p_s

end

section

variable {F ι M N : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_induction_nonempty (p : M → Prop) (p_mul : ∀ a b, p a → p b → p (a * b)) (hs : s ≠ ∅)
    (p_s : ∀ a ∈ s, p a) : p s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp at hs
  | cons a s hsa =>
    rw [Multiset.prod_cons]
    by_cases hs_empty : s = ∅
    · simp [hs_empty, p_s a]
    have hps : ∀ x, x ∈ s → p x := fun x hxs => p_s x (mem_cons_of_mem hxs)
    exact p_mul a s.prod (p_s a (mem_cons_self a s)) (hsa hs_empty hps)

end

section

variable {F ι M N : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_map_one : Multiset.prod (m.map fun _ => (1 : M)) = 1 := by
  rw [map_const', Multiset.prod_replicate, one_pow]

end

section

variable {F ι M N : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_map_toList (s : Multiset ι) (f : ι → M) : (s.toList.map f).prod = (s.map f).prod := by
  rw [← Multiset.prod_coe, ← Multiset.map_coe, coe_toList]

end

section

variable {F ι M N : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_pair (a b : M) : ({a, b} : Multiset M).prod = a * b := by
  rw [insert_eq_cons, Multiset.prod_cons, Multiset.prod_singleton]

end

section

variable {F ι M N : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_replicate (n : ℕ) (a : M) : (replicate n a).prod = a ^ n := by
  simp [replicate, List.prod_replicate]

end

section

variable {F ι M N : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_singleton (a : M) : Multiset.prod {a} = a := by
  simp only [mul_one, Multiset.prod_cons, ← cons_zero, Multiset.prod_zero]

end

section

variable {F ι M N : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_toList (s : Multiset M) : s.toList.prod = s.prod := by
  conv_rhs => rw [← coe_toList s]
  rw [Multiset.prod_coe]

end
