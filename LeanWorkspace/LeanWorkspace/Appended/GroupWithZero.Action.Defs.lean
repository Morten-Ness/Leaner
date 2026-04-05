import Mathlib

section

variable {M M₀ M₀' G₀ G₀' N A A' B α β : Type*}

variable (M₀ A) [MonoidWithZero M₀] [MonoidWithZero M₀'] [Zero A]

variable {M₀ A} [MulActionWithZero M₀ A] [Zero A'] [SMul M₀ A'] (p : Prop) [Decidable p]

theorem Pi.single_apply_smul {ι : Type*} [DecidableEq ι] (x : A) (i j : ι) :
    (Pi.single i 1 : ι → M₀) j • x = (Pi.single i x : ι → A) j := by
  rw [single_apply, ite_smul, one_smul, zero_smul, single_apply]

end

section

variable {M M₀ M₀' G₀ G₀' N A A' B α β : Type*}

variable {A} [Zero M₀] [Zero A] [SMulWithZero M₀ A]

variable {M₀} {a : M₀} {b : A}

theorem left_ne_zero_of_smul : a • b ≠ 0 → a ≠ 0 := mt fun h ↦ smul_eq_zero_of_left h b

end

section

variable {M M₀ M₀' G₀ G₀' N A A' B α β : Type*}

variable [Group α] [GroupWithZero β] [MulDistribMulAction α β]

theorem smul_div₀' (g : α) (x y : β) : g • (x / y) = (g • x) / (g • y) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, smul_mul', smul_inv₀']

end

section

variable {M M₀ M₀' G₀ G₀' N A A' B α β : Type*}

variable [Group α] [AddMonoid β] [DistribMulAction α β]

theorem smul_eq_zero_iff_eq (a : α) {x : β} : a • x = 0 ↔ x = 0 := ⟨fun h => by rw [← inv_smul_smul a x, h, smul_zero], fun h => h.symm ▸ smul_zero _⟩

end

section

variable {M M₀ M₀' G₀ G₀' N A A' B α β : Type*}

variable [GroupWithZero G₀] [GroupWithZero G₀'] [MulActionWithZero G₀ G₀']
  [SMulCommClass G₀ G₀' G₀'] [IsScalarTower G₀ G₀' G₀']

theorem smul_inv₀ (c : G₀) (x : G₀') : (c • x)⁻¹ = c⁻¹ • x⁻¹ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp only [inv_zero, zero_smul]
  obtain rfl | hx := eq_or_ne x 0
  · simp only [inv_zero, smul_zero]
  · refine inv_eq_of_mul_eq_one_left ?_
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, inv_mul_cancel₀ hx, one_smul]

end

section

variable {M M₀ M₀' G₀ G₀' N A A' B α β : Type*}

variable [AddGroup A] [DistribSMul M A]

theorem smul_neg (r : M) (x : A) : r • -x = -(r • x) := eq_neg_of_add_eq_zero_left <| by rw [← smul_add, neg_add_cancel, smul_zero]

end

section

variable {M M₀ M₀' G₀ G₀' N A A' B α β : Type*}

variable [AddGroup A] [DistribSMul M A]

theorem smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, smul_add, smul_neg]

end
