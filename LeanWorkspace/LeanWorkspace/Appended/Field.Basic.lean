import Mathlib

section

variable {K L : Type*}

variable [DivisionSemiring K] {a b c d : K}

theorem Commute.div_add_div (hbc : Commute b c) (hbd : Commute b d) (hb : b ≠ 0)
    (hd : d ≠ 0) : a / b + c / d = (a * d + b * c) / (b * d) := by
  rw [add_div, mul_div_mul_right _ b hd, hbc.eq, hbd.eq, mul_div_mul_right c d hb]

end

section

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

theorem Commute.div_sub_div (hbc : Commute b c) (hbd : Commute b d) (hb : b ≠ 0)
    (hd : d ≠ 0) : a / b - c / d = (a * d - b * c) / (b * d) := by
  simpa only [mul_neg, neg_div, ← sub_eq_add_neg] using hbc.neg_right.div_add_div hbd hb hd

end

section

variable {K L : Type*}

variable [DivisionSemiring K] {a b c d : K}

theorem Commute.inv_add_inv (hab : Commute a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    a⁻¹ + b⁻¹ = (a + b) / (a * b) := by
  rw [inv_eq_one_div, inv_eq_one_div, hab.one_div_add_one_div ha hb]

end

section

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

theorem Commute.inv_sub_inv (hab : Commute a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
  simp only [inv_eq_one_div, (Commute.one_right a).div_sub_div hab ha hb, one_mul, mul_one]

end

section

variable {K L : Type*}

variable [DivisionSemiring K] {a b c d : K}

theorem Commute.one_div_add_one_div (hab : Commute a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    1 / a + 1 / b = (a + b) / (a * b) := by
  rw [(Commute.one_right a).div_add_div hab ha hb, one_mul, mul_one, add_comm]

end

section

variable {K L : Type*}

variable [DivisionSemiring K] {a b c d : K}

theorem add_div' (a b c : K) (hc : c ≠ 0) : b + a / c = (b * c + a) / c := by
  rw [add_div, mul_div_cancel_right₀ _ hc]

end

section

variable {K L : Type*}

variable [DivisionSemiring K] {a b c d : K}

theorem add_div (a b c : K) : (a + b) / c = a / c + b / c := by simp_rw [div_eq_mul_inv, add_mul]

end

section

variable {K L : Type*}

variable [DivisionSemiring K] {a b c d : K}

theorem add_div_eq_mul_add_div (a b : K) (hc : c ≠ 0) : a + b / c = (a * c + b) / c := (eq_div_iff_mul_eq hc).2 <| by rw [right_distrib, div_mul_cancel₀ _ hc]

end

section

variable {K L : Type*}

variable [DivisionSemiring K] {a b c d : K}

theorem div_add' (a b c : K) (hc : c ≠ 0) : a / c + b = (a + b * c) / c := by
  rwa [add_comm, add_div', add_comm]

end

section

variable {K L : Type*}

variable [Semifield K] {a b d : K}

theorem div_add_div (a : K) (c : K) (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b + c / d = (a * d + b * c) / (b * d) := (Commute.all b _).div_add_div (Commute.all _ _) hb hd

end

section

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

theorem div_neg_self {a : K} (h : a ≠ 0) : a / -a = -1 := by rw [div_neg_eq_neg_div, div_self h]

end

section

variable {K L : Type*}

variable [Field K]

theorem div_sub' {a b c : K} (hc : c ≠ 0) : a / c - b = (a - c * b) / c := by
  simpa using div_sub_div a b hc one_ne_zero

-- see Note [lower instance priority]

end

section

variable {K L : Type*}

variable [Field K]

theorem div_sub_div (a : K) {b : K} (c : K) {d : K} (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b - c / d = (a * d - b * c) / (b * d) := (Commute.all b _).div_sub_div (Commute.all _ _) hb hd

end

section

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

theorem div_sub_div_same (a b c : K) : a / c - b / c = (a - b) / c := by
  rw [sub_eq_add_neg, ← neg_div, ← add_div, sub_eq_add_neg]

end

section

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

theorem div_sub_same {a b : K} (h : b ≠ 0) : (a - b) / b = a / b - 1 := by
  simpa only [← @div_self _ _ b h] using (div_sub_div_same a b b).symm

end

section

variable {K L : Type*}

variable [DivisionSemiring K] {a b c d : K}

theorem inv_add_inv' (ha : a ≠ 0) (hb : b ≠ 0) :
    a⁻¹ + b⁻¹ = a⁻¹ * (a + b) * b⁻¹ := let _ := invertibleOfNonzero ha; let _ := invertibleOfNonzero hb; invOf_add_invOf a b

end

section

variable {K L : Type*}

variable [Semifield K] {a b d : K}

theorem inv_add_inv (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ + b⁻¹ = (a + b) / (a * b) := (Commute.all a _).inv_add_inv ha hb

end

section

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

theorem inv_eq_self₀ {a : K} : a⁻¹ = a ↔ a = -1 ∨ a = 0 ∨ a = 1 := by
  obtain rfl | ha := eq_or_ne a 0; · simp
  rw [← mul_eq_one_iff_inv_eq₀ ha, ← pow_two, sq_eq_one_iff]
  tauto

end

section

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

theorem inv_sub_inv' {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ - b⁻¹ = a⁻¹ * (b - a) * b⁻¹ := let _ := invertibleOfNonzero ha; let _ := invertibleOfNonzero hb; invOf_sub_invOf a b

end

section

variable {K L : Type*}

variable [Field K]

theorem inv_sub_inv {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
  rw [inv_eq_one_div, inv_eq_one_div, div_sub_div _ _ ha hb, one_mul, mul_one]

end

section

variable {K L : Type*}

variable [Semifield K] {a b d : K}

theorem one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) : 1 / a + 1 / b = (a + b) / (a * b) := (Commute.all a _).one_div_add_one_div ha hb

end

section

variable {K L : Type*}

variable [DivisionSemiring K] {a b c d : K}

theorem one_div_mul_add_mul_one_div_eq_one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) :
    1 / a * (a + b) * (1 / b) = 1 / a + 1 / b := by
  simpa only [one_div] using (inv_add_inv' ha hb).symm

end

section

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

theorem one_div_mul_sub_mul_one_div_eq_one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) :
    1 / a * (b - a) * (1 / b) = 1 / a - 1 / b := by
  simpa only [one_div] using (inv_sub_inv' ha hb).symm

end

section

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

theorem same_sub_div {a b : K} (h : b ≠ 0) : (b - a) / b = 1 - a / b := by
  simpa only [← @div_self _ _ b h] using (div_sub_div_same b a b).symm

end

section

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

theorem self_eq_inv₀ {a : K} : a = a⁻¹ ↔ a = -1 ∨ a = 0 ∨ a = 1 := by
  rw [eq_comm, inv_eq_self₀]

-- see Note [lower instance priority]

end

section

variable {K L : Type*}

variable [Field K]

theorem sub_div' {a b c : K} (hc : c ≠ 0) : b - a / c = (b * c - a) / c := by
  simpa using div_sub_div b a one_ne_zero hc

end

section

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

variable [NeZero (2 : K)]

theorem sub_half (a : K) : a - a / 2 = a / 2 := by rw [sub_eq_iff_eq_add, add_halves]

end
