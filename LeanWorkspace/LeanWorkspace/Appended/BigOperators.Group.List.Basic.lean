import Mathlib

section

variable {ι α β M N P G : Type*}

variable [CommMonoid M] {a : M} {l l₁ l₂ : List M}

theorem CommMonoid.mul_prod_eraseIdx {i} (h : i < l.length) : l[i] * (l.eraseIdx i).prod = l.prod := List.mul_prod_eraseIdx h (fun a' _ ↦ Commute.all l[i] a')

end

section

variable {ι α β M N P G : Type*}

variable [CommMonoid M] {a : M} {l l₁ l₂ : List M}

theorem CommMonoid.prod_insertIdx {i} (h : i ≤ l.length) : (l.insertIdx i a).prod = a * l.prod := List.prod_insertIdx h (fun a' _ ↦ Commute.all a a')

end

section

variable {ι α β M N P G : Type*}

theorem headI_le_sum (L : List ℕ) : L.headI ≤ L.sum := Nat.le.intro (List.headI_add_tail_sum L)

end

section

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem headI_mul_tail_prod_of_ne_nil [Inhabited M] (l : List M) (h : l ≠ []) :
    l.headI * l.tail.prod = l.prod := by cases l <;> [contradiction; simp]

end

section

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem length_pos_of_one_lt_prod [Preorder M] (L : List M) (h : 1 < L.prod) : 0 < L.length := List.length_pos_of_prod_ne_one L h.ne'

end

section

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem length_pos_of_prod_lt_one [Preorder M] (L : List M) (h : L.prod < 1) : 0 < L.length := List.length_pos_of_prod_ne_one L h.ne

end

section

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem length_pos_of_prod_ne_one (L : List M) (h : L.prod ≠ 1) : 0 < L.length := by
  cases L
  · simp at h
  · simp

end

section

variable {ι α β M N P G : Type*}

variable [CommMonoid M] {a : M} {l l₁ l₂ : List M}

theorem prod_erase [DecidableEq M] (ha : a ∈ l) : a * (l.erase a).prod = l.prod := List.prod_erase_of_comm ha fun x _ y _ ↦ mul_comm x y

end

section

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem prod_hom_nonempty {l : List M} {F : Type*} [FunLike F M N] [MulHomClass F M N] (f : F)
    (hl : l ≠ []) : (l.map f).prod = f l.prod := match l, hl with | x :: xs, hl => by induction xs generalizing x <;> simp_all

end

section

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem prod_hom₂_nonempty {l : List ι} (f : M → N → P)
    (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d) (f₁ : ι → M) (f₂ : ι → N) (hl : l ≠ []) :
    (l.map fun i => f (f₁ i) (f₂ i)).prod = f (l.map f₁).prod (l.map f₂).prod := by
  match l, hl with | x :: xs, hl => induction xs generalizing x <;> simp_all

end

section

variable {ι α β M N P G : Type*}

theorem prod_int_mod (l : List ℤ) (n : ℤ) : l.prod % n = (l.map (· % n)).prod % n := by
  induction l <;> simp [Int.mul_emod, *]

end

section

variable {ι α β M N P G : Type*}

variable [CommMonoid M] {a : M} {l l₁ l₂ : List M}

theorem prod_map_filter_mul_prod_map_filter_not (p : α → Prop) [DecidablePred p] (f : α → M)
    (l : List α) :
    ((l.filter p).map f).prod * ((l.filter fun x => ¬p x).map f).prod = (l.map f).prod := by
  rw [← List.prod_map_ite]
  simp only [ite_self]

end

section

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem prod_map_mul {M : Type*} [CommMonoid M] {l : List ι} {f g : ι → M} :
    (l.map fun i => f i * g i).prod = (l.map f).prod * (l.map g).prod := List.prod_hom₂ l (· * ·) mul_mul_mul_comm (mul_one _) _ _

end

section

variable {ι α β M N P G : Type*}

theorem sum_int_mod (l : List ℤ) (n : ℤ) : l.sum % n = (l.map (· % n)).sum % n := by
  induction l <;> simp [Int.add_emod, *]

end

section

variable {ι α β M N P G : Type*}

theorem tail_sum (L : List ℕ) : L.tail.sum = L.sum - L.headI := by
  rw [← List.headI_add_tail_sum L, add_comm, Nat.add_sub_cancel_right]

end
