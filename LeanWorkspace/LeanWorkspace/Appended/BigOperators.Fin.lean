import Mathlib

section

variable {ι M : Type*}

theorem prod_range [CommMonoid M] {n : ℕ} (f : ℕ → M) :
    ∏ i ∈ Finset.range n, f i = ∏ i : Fin n, f i := (Fin.prod_univ_eq_prod_range _ _).symm

end

section

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_univ_def (f : Fin n → M) : ∏ i, f i = ((List.finRange n).map f).prod := by
  rw [← List.ofFn_eq_map, Fin.prod_ofFn]

end

section

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_univ_eight (f : Fin 8 → M) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 := by
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_seven]
  rfl

end

section

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_univ_five (f : Fin 5 → M) : ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 := by
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_four]
  rfl

end

section

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_univ_four (f : Fin 4 → M) : ∏ i, f i = f 0 * f 1 * f 2 * f 3 := by
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_three]
  rfl

end

section

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_univ_fun_getElem (l : List ι) (f : ι → M) :
    ∏ i : Fin l.length, f l[i.1] = (l.map f).prod := by
  simp [Finset.prod_eq_multiset_prod]

end

section

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_univ_getElem (l : List M) : ∏ i : Fin l.length, l[i.1] = l.prod := by
  simp [Finset.prod_eq_multiset_prod]

end

section

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_univ_seven (f : Fin 7 → M) : ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 := by
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_six]
  rfl

end

section

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_univ_six (f : Fin 6 → M) : ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 := by
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_five]
  rfl

end

section

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_univ_three (f : Fin 3 → M) : ∏ i, f i = f 0 * f 1 * f 2 := by
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_two]
  rfl

end
