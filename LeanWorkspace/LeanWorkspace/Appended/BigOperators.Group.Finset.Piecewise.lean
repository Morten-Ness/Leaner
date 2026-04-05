import Mathlib

section

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_ite_mem [DecidableEq ι] (s t : Finset ι) (f : ι → M) :
    ∏ i ∈ s, (if i ∈ t then f i else 1) = ∏ i ∈ s ∩ t, f i := by
  rw [← Finset.prod_filter, Finset.filter_mem_eq_inter]

end

section

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem dvd_prod_of_mem (f : ι → M) {a : ι} {s : Finset ι} (ha : a ∈ s) : f a ∣ ∏ i ∈ s, f i := by
  classical
    rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem ha]
    exact dvd_mul_right _ _

end

section

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_apply_ite_of_false {p : ι → Prop} [DecidablePred p] (f g : ι → γ) (k : γ → M)
    (h : ∀ x ∈ s, ¬p x) : (∏ x ∈ s, k (if p x then f x else g x)) = ∏ x ∈ s, k (g x) := by
  simp_rw [apply_ite k]
  exact Finset.prod_ite_of_false h _ _

end

section

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_apply_ite_of_true {p : ι → Prop} [DecidablePred p] (f g : ι → γ) (k : γ → M)
    (h : ∀ x ∈ s, p x) : (∏ x ∈ s, k (if p x then f x else g x)) = ∏ x ∈ s, k (f x) := by
  simp_rw [apply_ite k]
  exact Finset.prod_ite_of_true h _ _

end

section

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_attach_eq_prod_dite [Fintype ι] (s : Finset ι) (f : s → M) [DecidablePred (· ∈ s)] :
    ∏ i ∈ s.attach, f i = ∏ i, if h : i ∈ s then f ⟨i, h⟩ else 1 := by
  rw [Finset.prod_dite, Finset.univ_eq_attach, Finset.prod_const_one, mul_one]
  congr
  · simp
  · ext; simp
  · apply Function.hfunext <;> simp +contextual [Subtype.heq_iff_coe_eq]

end

section

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_eq_mul_prod_diff_singleton [DecidableEq ι] {s : Finset ι} (i : ι) (f : ι → M)
    (h : i ∉ s → f i = 1) : ∏ x ∈ s, f x = f i * ∏ x ∈ s \ {i}, f x := by
  by_cases hs : i ∈ s
  · convert (Finset.prod_inter_mul_prod_diff s {i} f).symm
    simp [hs]
  · simp_all only [not_false_eq_true, forall_const, one_mul]
    apply Finset.prod_congr <;> aesop

end

section

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_eq_mul_prod_diff_singleton_of_mem [DecidableEq ι] {s : Finset ι} {i : ι} (h : i ∈ s)
    (f : ι → M) : ∏ x ∈ s, f x = f i * ∏ x ∈ s \ {i}, f x := Finset.prod_eq_mul_prod_diff_singleton _ _ (by simp_all)

end

section

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_eq_prod_diff_singleton_mul [DecidableEq ι] {s : Finset ι} {i : ι} (h : i ∈ s)
    (f : ι → M) : ∏ x ∈ s, f x = (∏ x ∈ s \ {i}, f x) * f i := by
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem h, mul_comm]

end

section

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_inter_mul_prod_diff [DecidableEq ι] (s t : Finset ι) (f : ι → M) :
    (∏ x ∈ s ∩ t, f x) * ∏ x ∈ s \ t, f x = ∏ x ∈ s, f x := by
  convert (Finset.prod_piecewise s t f f).symm
  simp +unfoldPartialApp [Finset.piecewise]

end

section

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_ite {s : Finset ι} {p : ι → Prop} [DecidablePred p] (f g : ι → M) :
    ∏ x ∈ s, (if p x then f x else g x) = (∏ x ∈ s with p x, f x) * ∏ x ∈ s with ¬p x, g x := by
  simp [Finset.prod_apply_ite _ _ fun x => x]

end

section

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M] [Fintype ι]

theorem prod_ite_eq_ite_exists (p : ι → Prop) [DecidablePred p] (h : ∀ i j, p i → p j → i = j)
    (a : M) : ∏ i, ite (p i) a 1 = ite (∃ i, p i) a 1 := by
  simp [Finset.prod_ite_one Finset.univ p (by simpa using h)]

end

section

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_ite_eq_of_mem' [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M) (h : a ∈ s) :
    (∏ x ∈ s, if x = a then b x else 1) = b a := by
  simp only [Finset.prod_ite_eq', if_pos h]

end

section

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_ite_eq_of_mem [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M) (h : a ∈ s) :
    (∏ x ∈ s, if a = x then b x else 1) = b a := by
  simp only [Finset.prod_ite_eq, if_pos h]

end
