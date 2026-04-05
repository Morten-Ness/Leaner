import Mathlib

section

variable {ι A M : Type*} [AddMonoid A] [CommMonoid M]

theorem coe_prod (s : Finset ι) (ψ : ι → AddChar A M) : ∏ i ∈ s, ψ i = ∏ i ∈ s, ⇑(ψ i) := by
  induction s using Finset.cons_induction <;> simp [*]

end

section

variable {ι A M : Type*} [AddMonoid A] [CommMonoid M]

theorem coe_sum (s : Finset ι) (ψ : ι → AddChar A M) : ∑ i ∈ s, ψ i = ∏ i ∈ s, ⇑(ψ i) := by
  induction s using Finset.cons_induction <;> simp [*]

end

section

variable {A B M N : Type*} [AddMonoid A] [AddMonoid B] [Monoid M] [Monoid N] {ψ : AddChar A M}

theorem compAddMonoidHom_injective_left (f : A →+ B) (hf : Function.Surjective f) :
    Function.Injective fun ψ : AddChar B M ↦ ψ.compAddMonoidHom f := by
  rintro ψ χ h; rw [DFunLike.ext'_iff] at h ⊢; exact hf.injective_comp_right h

end

section

variable {A B M N : Type*} [AddMonoid A] [AddMonoid B] [Monoid M] [Monoid N] {ψ : AddChar A M}

theorem compAddMonoidHom_injective_right (ψ : AddChar B M) (hψ : Function.Injective ψ) :
    Function.Injective fun f : A →+ B ↦ ψ.compAddMonoidHom f := by
  rintro f g h
  rw [DFunLike.ext'_iff] at h ⊢; exact hψ.comp_left h

end

section

variable {A M : Type*} [AddCommGroup A] [DivisionCommMonoid M]

theorem div_apply' (ψ χ : AddChar A M) (a : A) : (ψ / χ) a = ψ a / χ a := by
  rw [AddChar.div_apply, AddChar.map_neg_eq_inv, div_eq_mul_inv]

end

section

variable {A M : Type*} [AddCommGroup A] [DivisionCommMonoid M]

theorem injective_iff {ψ : AddChar A M} : Function.Injective ψ ↔ ∀ ⦃x⦄, ψ x = 1 → x = 0 := ψ.toMonoidHom.ker_eq_bot_iff.symm.trans eq_bot_iff

end

section

variable {A B M N : Type*} [AddMonoid A] [AddMonoid B] [Monoid M] [Monoid N] {ψ : AddChar A M}

theorem ne_zero_iff : ψ ≠ 0 ↔ ∃ x, ψ x ≠ 1 := DFunLike.ne_iff

noncomputable instance : DecidableEq (AddChar A M) := Classical.decEq _

end

section

variable {ι A M : Type*} [AddMonoid A] [CommMonoid M]

theorem prod_apply (s : Finset ι) (ψ : ι → AddChar A M) (a : A) :
    (∏ i ∈ s, ψ i) a = ∏ i ∈ s, ψ i a := by rw [AddChar.coe_prod, Finset.prod_apply]

end

section

variable {A M : Type*} [AddCommGroup A] [DivisionCommMonoid M]

theorem sub_apply' (ψ χ : AddChar A M) (a : A) : (ψ - χ) a = ψ a / χ a := by
  rw [AddChar.sub_apply, AddChar.map_neg_eq_inv, div_eq_mul_inv]

end

section

variable {ι A M : Type*} [AddMonoid A] [CommMonoid M]

theorem sum_apply (s : Finset ι) (ψ : ι → AddChar A M) (a : A) :
    (∑ i ∈ s, ψ i) a = ∏ i ∈ s, ψ i a := by rw [AddChar.coe_sum, Finset.prod_apply]

end

section

variable {A R : Type*} [AddGroup A] [Fintype A] [CommSemiring R] [IsDomain R]
  {ψ : AddChar A R}

variable [CharZero R]

theorem sum_eq_zero_iff_ne_zero : ∑ x, ψ x = 0 ↔ ψ ≠ 0 := by
  classical
  rw [AddChar.sum_eq_ite, Ne.ite_eq_right_iff]; exact Nat.cast_ne_zero.2 Fintype.card_ne_zero

end

section

variable {A R : Type*} [AddGroup A] [Fintype A] [CommSemiring R] [IsDomain R]
  {ψ : AddChar A R}

variable [CharZero R]

theorem sum_ne_zero_iff_eq_zero : ∑ x, ψ x ≠ 0 ↔ ψ = 0 := AddChar.sum_eq_zero_iff_ne_zero.not_left

end

section

theorem val_isUnit {A M} [AddGroup A] [Monoid M] (φ : AddChar A M) (a : A) : IsUnit (φ a) := IsUnit.map φ.toMonoidHom <| Group.isUnit (Multiplicative.ofAdd a)

end
