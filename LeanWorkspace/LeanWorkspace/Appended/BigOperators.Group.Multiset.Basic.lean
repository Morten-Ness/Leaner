import Mathlib

section

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem dvd_prod : a ∈ s → a ∣ s.prod := Quotient.inductionOn s (fun l a h ↦ by simpa using List.dvd_prod h) a

end

section

variable {F ι κ G M N O : Type*}

theorem prod_dvd_prod_of_dvd [CommMonoid N] {S : Multiset M} (g1 g2 : M → N)
    (h : ∀ a ∈ S, g1 a ∣ g2 a) : (Multiset.map g1 S).prod ∣ (Multiset.map g2 S).prod := by
  apply Multiset.induction_on' S
  · simp
  intro a T haS _ IH
  simp [mul_dvd_mul (h a haS) IH]

end

section

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_dvd_prod_of_le (h : s ≤ t) : s.prod ∣ t.prod := by
  obtain ⟨z, rfl⟩ := exists_add_of_le h
  simp only [Multiset.prod_add, dvd_mul_right]

end

section

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_eq_one (h : ∀ x ∈ s, x = (1 : M)) : s.prod = 1 := by
  induction s using Quotient.inductionOn; simp [List.prod_eq_one h]

end

section

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_eq_pow_single [DecidableEq M] (a : M) (h : ∀ a' ≠ a, a' ∈ s → a' = 1) :
    s.prod = a ^ s.count a := by
  induction s using Quotient.inductionOn; simp [List.prod_eq_pow_single a h]

end

section

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_hom_ne_zero {s : Multiset M} (hs : s ≠ 0) {F : Type*} [FunLike F M N]
    [MulHomClass F M N] (f : F) :
    (s.map f).prod = f s.prod := by
  induction s using Quot.inductionOn; aesop (add simp List.prod_hom_nonempty)

end

section

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_hom₂_ne_zero [CommMonoid O] {s : Multiset ι} (hs : s ≠ 0) (f : M → N → O)
    (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d) (f₁ : ι → M) (f₂ : ι → N) :
    (s.map fun i => f (f₁ i) (f₂ i)).prod = f (s.map f₁).prod (s.map f₂).prod := by
  induction s using Quotient.inductionOn; aesop (add simp List.prod_hom₂_nonempty)

end

section

variable {F ι κ G M N O : Type*}

theorem prod_int_mod (s : Multiset ℤ) (n : ℤ) : s.prod % n = (s.map (· % n)).prod % n := by
  induction s using Multiset.induction <;> simp [Int.mul_emod, *]

end

section

variable {F ι κ G M N O : Type*}

variable [DivisionCommMonoid G] {m : Multiset ι} {f g : ι → G}

theorem prod_map_div : (m.map fun i => f i / g i).prod = (m.map f).prod / (m.map g).prod := Multiset.prod_hom₂ m (· / ·) mul_div_mul_comm (div_one _) _ _

end

section

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_map_eq_pow_single [DecidableEq ι] (i : ι)
    (hf : ∀ i' ≠ i, i' ∈ m → f i' = 1) : (m.map f).prod = f i ^ m.count i := by
  induction m using Quotient.inductionOn
  simp [List.prod_map_eq_pow_single i f hf]

end

section

variable {F ι κ G M N O : Type*}

variable [DivisionCommMonoid G] {m : Multiset ι} {f g : ι → G}

theorem prod_map_inv' (m : Multiset G) : (m.map Inv.inv).prod = m.prod⁻¹ := Multiset.prod_hom m (invMonoidHom : G →* G)

end

section

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_map_mul : (m.map fun i => f i * g i).prod = (m.map f).prod * (m.map g).prod := Multiset.prod_hom₂ m (· * ·) mul_mul_mul_comm (mul_one _) _ _

end

section

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_map_pow {n : ℕ} : (m.map fun i => f i ^ n).prod = (m.map f).prod ^ n := Multiset.prod_hom' m (powMonoidHom n : M →* M) f

end

section

variable {F ι κ G M N O : Type*}

theorem prod_nat_mod (s : Multiset ℕ) (n : ℕ) : s.prod % n = (s.map (· % n)).prod % n := by
  induction s using Multiset.induction <;> simp [Nat.mul_mod, *]

end

section

variable {F ι κ G M N O : Type*}

theorem sum_int_mod (s : Multiset ℤ) (n : ℤ) : s.sum % n = (s.map (· % n)).sum % n := by
  induction s using Multiset.induction <;> simp [Int.add_emod, *]

end

section

variable {F ι κ G M N O : Type*}

theorem sum_map_singleton (s : Multiset M) : (s.map fun a => ({a} : Multiset M)).sum = s := Multiset.induction_on s (by simp) (by simp)

end

section

variable {F ι κ G M N O : Type*}

theorem sum_nat_mod (s : Multiset ℕ) (n : ℕ) : s.sum % n = (s.map (· % n)).sum % n := by
  induction s using Multiset.induction <;> simp [Nat.add_mod, *]

end
