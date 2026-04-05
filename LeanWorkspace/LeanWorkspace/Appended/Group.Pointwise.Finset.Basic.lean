import Mathlib

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Group α] [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β]

variable (f : F) {s t : Finset α} {a b : α}

theorem Nonempty.one_mem_div (h : s.Nonempty) : (1 : α) ∈ s / s := let ⟨a, ha⟩ := h
  Finset.mem_div.2 ⟨a, ha, a, ha, div_self' _⟩

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [Mul α] [IsLeftCancelMul α] [DecidableEq α] {s t : Finset α} {a : α}

theorem Nontrivial.mul_left : t.Nontrivial → s.Nonempty → (s * t).Nontrivial := by
  rintro ⟨a, ha, b, hb, hab⟩ ⟨c, hc⟩
  exact ⟨c * a, Finset.mul_mem_mul hc ha, c * b, Finset.mul_mem_mul hc hb, by simpa⟩

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [Mul α] [IsRightCancelMul α] [DecidableEq α] {s t : Finset α} {a : α}

theorem Nontrivial.mul_right : s.Nontrivial → t.Nonempty → (s * t).Nontrivial := by
  rintro ⟨a, ha, b, hb, hab⟩ ⟨c, hc⟩
  exact ⟨a * c, Finset.mul_mem_mul ha hc, b * c, Finset.mul_mem_mul hb hc, by simpa⟩

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

theorem coe_list_prod (s : List (Finset α)) : (↑s.prod : Set α) = (s.map (↑)).prod := map_list_prod (Finset.coeMonoidHom : Finset α →* Set α) _

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

theorem coe_pow (s : Finset α) (n : ℕ) : ↑(s ^ n) = (s : Set α) ^ n := by
  change ↑(npowRec n s) = (s : Set α) ^ n
  induction n with
  | zero => rw [npowRec, pow_zero, Finset.coe_one]
  | succ n ih => rw [npowRec, pow_succ, Finset.coe_mul, ih]

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

theorem empty_pow (hn : n ≠ 0) : (∅ : Finset α) ^ n = ∅ := match n with | n + 1 => by simp [pow_succ]

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [InvolutiveInv α] {s : Finset α} {a : α}

theorem inv_product [DecidableEq β] [InvolutiveInv β] (s : Finset α) (t : Finset β) :
    (s ×ˢ t)⁻¹ = s⁻¹ ×ˢ t⁻¹ := mod_cast (s : Set α).inv_prod (t : Set β)

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Group α] [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β]

variable (f : F) {s t : Finset α} {a b : α}

theorem isUnit_iff_singleton : IsUnit s ↔ ∃ a, s = {a} := by
  simp only [Finset.isUnit_iff, Group.isUnit, and_true]

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Group α] [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β]

variable (f : F) {s t : Finset α} {a b : α}

theorem isUnit_iff_singleton_aux {α} [Group α] {s : Finset α} :
    (∃ a, s = {a} ∧ IsUnit a) ↔ ∃ a, s = {a} := by
  simp only [Group.isUnit, and_true]

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [InvolutiveInv α] {s : Finset α} {a : α}

theorem mem_inv' : a ∈ s⁻¹ ↔ a⁻¹ ∈ s := by simp [Finset.mem_inv, inv_eq_iff_eq_inv]

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Group α] [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β]

variable (f : F) {s t : Finset α} {a b : α}

theorem one_notMem_inv_mul_iff : (1 : α) ∉ t⁻¹ * s ↔ Disjoint s t := Finset.one_mem_inv_mul_iff.not_left

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

theorem pow_subset_pow (hst : s ⊆ t) (ht : 1 ∈ t) (hmn : m ≤ n) : s ^ m ⊆ t ^ n := (Finset.pow_subset_pow_left hst).trans (Finset.pow_subset_pow_right ht hmn)

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]
  (f : F) {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem product_mul_product_comm [DecidableEq β] (s₁ s₂ : Finset α) (t₁ t₂ : Finset β) :
    (s₁ ×ˢ t₁) * (s₂ ×ˢ t₂) = (s₁ * s₂) ×ˢ (t₁ * t₂) := mod_cast (s₁ : Set α).prod_mul_prod_comm s₂ (t₁ : Set β) t₂

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [MulOneClass α]

theorem subset_mul_left (s : Finset α) {t : Finset α} (ht : (1 : α) ∈ t) : s ⊆ s * t := fun a ha =>
  Finset.mem_mul.2 ⟨a, ha, 1, ht, mul_one _⟩

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [MulOneClass α]

theorem subset_mul_right {s : Finset α} (t : Finset α) (hs : (1 : α) ∈ s) : t ⊆ s * t := fun a ha =>
  Finset.mem_mul.2 ⟨1, hs, a, ha, one_mul _⟩

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

theorem subset_pow (hs : 1 ∈ s) (hn : n ≠ 0) : s ⊆ s ^ n := by
  simpa using Finset.pow_subset_pow_right hs <| Nat.one_le_iff_ne_zero.2 hn

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [One α]

theorem toFinset_one : (1 : Set α).toFinset = 1 := rfl

-- should take simp priority over `Finite.toFinset_singleton`

end
