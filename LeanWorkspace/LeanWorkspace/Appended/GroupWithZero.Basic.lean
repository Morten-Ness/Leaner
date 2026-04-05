import Mathlib

section

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a b x : G₀}

theorem GroupWithZero.mul_left_injective (h : x ≠ 0) :
    Function.Injective fun y => y * x := fun y y' w => by
  simpa only [mul_assoc, mul_inv_cancel₀ h, mul_one] using congr_arg (fun y => y * x⁻¹) w

end

section

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a b x : G₀}

theorem GroupWithZero.mul_right_injective (h : x ≠ 0) :
    Function.Injective fun y => x * y := fun y y' w => by
  simpa only [← mul_assoc, inv_mul_cancel₀ h, one_mul] using congr_arg (fun y => x⁻¹ * y) w

end

section

variable {M₀ G₀ : Type*}

variable {R S : Type*} {x y : R}

theorem IsNilpotent.of_pow [MonoidWithZero R] {x : R} {m : ℕ}
    (h : IsNilpotent (x ^ m)) : IsNilpotent x := have ⟨n, h⟩ := h
  ⟨m * n, by rw [← h, pow_mul x m n]⟩

end

section

variable {M₀ G₀ : Type*}

variable {R S : Type*} {x y : R}

theorem IsNilpotent.pow_of_pos {n} {S : Type*} [MonoidWithZero S] {x : S}
    (hx : IsNilpotent x) (hn : n ≠ 0) : IsNilpotent (x ^ n) := by
  cases n with
  | zero => contradiction
  | succ => exact IsNilpotent.pow_succ _ hx

end

section

variable {M₀ G₀ : Type*}

variable {R S : Type*} {x y : R}

theorem IsNilpotent.pow_succ (n : ℕ) {S : Type*} [MonoidWithZero S] {x : S}
    (hx : IsNilpotent x) : IsNilpotent (x ^ n.succ) := have ⟨N, hN⟩ := hx
  ⟨N, by rw [← pow_mul, Nat.succ_mul, pow_add, hN, mul_zero]⟩

end

section

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem div_div_self (a : G₀) : a / (a / a) = a := by
  rw [div_div_eq_mul_div]
  exact mul_self_div_self a

end

section

variable {M₀ G₀ : Type*}

variable [CommGroupWithZero G₀]

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem div_mul_eq_mul_div₀ (a b c : G₀) : a / c * b = a * b / c := by
  simp_rw [div_eq_mul_inv, mul_assoc, mul_comm c⁻¹]

end

section

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem div_self_mul_self' (a : G₀) : a / (a * a) = a⁻¹ := calc
    a / (a * a) = a⁻¹⁻¹ * a⁻¹ * a⁻¹ := by simp [mul_inv_rev]
    _ = a⁻¹ := inv_mul_mul_self _

end

section

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem div_self_mul_self (a : G₀) : a / a * a = a := by rw [div_eq_mul_inv, mul_inv_mul_cancel a]

attribute [local simp] div_eq_mul_inv mul_comm mul_assoc mul_left_comm

end

section

variable {M₀ G₀ : Type*}

variable [CommGroupWithZero G₀]

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem div_sq_cancel (a b : G₀) : a ^ 2 * b / a = a * b := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · rw [sq, mul_assoc, mul_div_cancel_left₀ _ ha]

end

section

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem div_zero (a : G₀) : a / 0 = 0 := by rw [div_eq_mul_inv, inv_zero, mul_zero]

end

section

variable {M₀ G₀ : Type*}

variable [MulZeroOneClass M₀]

theorem eq_of_zero_eq_one (h : (0 : M₀) = 1) (a b : M₀) : a = b := @Subsingleton.elim _ (subsingleton_of_zero_eq_one h) a b

end

section

variable {M₀ G₀ : Type*}

variable {a b c : M₀}

variable [MulZeroOneClass M₀]

theorem eq_zero_of_mul_eq_self_left [IsRightCancelMulZero M₀] (h₁ : b ≠ 1) (h₂ : b * a = a) :
    a = 0 := Classical.byContradiction fun ha => h₁ <| mul_right_cancel₀ ha <| h₂.symm ▸ (one_mul a).symm

end

section

variable {M₀ G₀ : Type*}

variable {a b c : M₀}

variable [MulZeroOneClass M₀]

theorem eq_zero_of_mul_eq_self_right [IsLeftCancelMulZero M₀] (h₁ : b ≠ 1) (h₂ : a * b = a) :
    a = 0 := Classical.byContradiction fun ha => h₁ <| mul_left_cancel₀ ha <| h₂.symm ▸ (mul_one a).symm

end

section

variable {M₀ G₀ : Type*}

variable [Mul M₀] [Zero M₀] [NoZeroDivisors M₀] {a b : M₀}

theorem eq_zero_of_mul_self_eq_zero (h : a * a = 0) : a = 0 := (eq_zero_or_eq_zero_of_mul_eq_zero h).elim id id

end

section

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem eq_zero_of_one_div_eq_zero {a : G₀} (h : 1 / a = 0) : a = 0 := Classical.byCases (fun ha => ha) fun ha => ((one_div_ne_zero ha) h).elim

end

section

variable {M₀ G₀ : Type*}

variable [MulZeroOneClass M₀]

theorem eq_zero_of_zero_eq_one (h : (0 : M₀) = 1) (a : M₀) : a = 0 := by
  rw [← mul_one a, ← h, mul_zero]

end

section

variable {M₀ G₀ : Type*}

variable {R S : Type*} {x y : R}

theorem exists_isNilpotent_of_not_isReduced {R : Type*} [Zero R] [Pow R ℕ] (h : ¬IsReduced R) :
    ∃ x : R, x ≠ 0 ∧ IsNilpotent x := by
  simpa [isReduced_iff, not_forall, and_comm] using h

end

section

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀] {a : M₀} {n : ℕ}

variable [IsReduced M₀]

theorem exists_right_inv_of_exists_left_inv {α} [MonoidWithZero α]
    (h : ∀ a : α, a ≠ 0 → ∃ b : α, b * a = 1) {a : α} (ha : a ≠ 0) : ∃ b : α, a * b = 1 := by
  obtain _ | _ := subsingleton_or_nontrivial α
  · exact ⟨a, Subsingleton.elim _ _⟩
  obtain ⟨b, hb⟩ := h a ha
  obtain ⟨c, hc⟩ := h b (left_ne_zero_of_mul <| hb.trans_ne one_ne_zero)
  refine ⟨b, ?_⟩
  conv_lhs => rw [← one_mul (a * b), ← hc, mul_assoc, ← mul_assoc b, hb, one_mul, hc]

end

section

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem inv_eq_zero {a : G₀} : a⁻¹ = 0 ↔ a = 0 := by rw [inv_eq_iff_eq_inv, inv_zero]

end

section

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a b x : G₀}

theorem inv_mul_cancel_left₀ (h : a ≠ 0) (b : G₀) : a⁻¹ * (a * b) = b := calc
    a⁻¹ * (a * b) = a⁻¹ * a * b := (mul_assoc _ _ _).symm
    _ = b := by simp [h]

end

section

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a b x : G₀}

theorem inv_mul_cancel_right₀ (h : b ≠ 0) (a : G₀) : a * b⁻¹ * b = a := calc
    a * b⁻¹ * b = a * (b⁻¹ * b) := mul_assoc _ _ _
    _ = a := by simp [h]

end

section

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem inv_mul_mul_self (a : G₀) : a⁻¹ * a * a = a := by
  by_cases h : a = 0
  · rw [h, inv_zero, mul_zero]
  · rw [inv_mul_cancel₀ h, one_mul]

end

section

variable {M₀ G₀ : Type*}

variable {R S : Type*} {x y : R}

theorem isNilpotent_iff_eq_zero [MonoidWithZero R] [IsReduced R] : IsNilpotent x ↔ x = 0 := ⟨fun h => h.eq_zero, fun h => h.symm ▸ IsNilpotent.zero⟩

end

section

variable {M₀ G₀ : Type*}

variable [MulZeroClass M₀] {a b : M₀}

theorem left_ne_zero_of_mul : a * b ≠ 0 → a ≠ 0 := mt fun h => mul_eq_zero_of_left h b

end

section

variable {M₀ G₀ : Type*}

variable [MulZeroOneClass M₀] [Nontrivial M₀] {a b : M₀}

theorem left_ne_zero_of_mul_eq_one (h : a * b = 1) : a ≠ 0 := left_ne_zero_of_mul <| ne_zero_of_eq_one h

end

section

variable {M₀ G₀ : Type*}

variable {a b c : M₀}

variable [MulZeroOneClass M₀]

theorem mul_eq_left₀ [IsLeftCancelMulZero M₀] (ha : a ≠ 0) : a * b = a ↔ b = 1 := by
  rw [Iff.comm, ← mul_right_inj' ha, mul_one]

end

section

variable {M₀ G₀ : Type*}

variable {a b c : M₀}

variable [MulZeroOneClass M₀]

theorem mul_eq_right₀ [IsRightCancelMulZero M₀] (hb : b ≠ 0) : a * b = b ↔ a = 1 := by
  rw [Iff.comm, ← mul_left_inj' hb, one_mul]

end

section

variable {M₀ G₀ : Type*}

variable [MulZeroClass M₀] {a b : M₀}

theorem mul_eq_zero_of_ne_zero_imp_eq_zero {a b : M₀} (h : a ≠ 0 → b = 0) : a * b = 0 := by
  have : Decidable (a = 0) := Classical.propDecidable (a = 0)
  exact if ha : a = 0 then by rw [ha, zero_mul] else by rw [h ha, mul_zero]

end

section

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem mul_inv_mul_cancel (a : G₀) : a * a⁻¹ * a = a := by
  by_cases h : a = 0
  · rw [h, inv_zero, mul_zero]
  · rw [mul_inv_cancel₀ h, one_mul]

end

section

variable {M₀ G₀ : Type*}

variable {a b c : M₀}

variable [MulZeroOneClass M₀]

theorem mul_left_eq_self₀ [IsRightCancelMulZero M₀] : a * b = b ↔ a = 1 ∨ b = 0 := calc
    a * b = b ↔ a * b = 1 * b := by rw [one_mul]
    _ ↔ a = 1 ∨ b = 0 := mul_eq_mul_right_iff

end

section

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem mul_left_surjective₀ {a : G₀} (h : a ≠ 0) : Function.Surjective fun g => a * g := fun g =>
  ⟨a⁻¹ * g, by simp [← mul_assoc, mul_inv_cancel₀ h]⟩

end

section

variable {M₀ G₀ : Type*}

variable [Mul M₀] [Zero M₀] [NoZeroDivisors M₀] {a b : M₀}

theorem mul_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := mt eq_zero_or_eq_zero_of_mul_eq_zero <| not_or.mpr ⟨ha, hb⟩

end

section

variable {M₀ G₀ : Type*}

variable {a b c : M₀}

variable [MulZeroOneClass M₀]

theorem mul_right_eq_self₀ [IsLeftCancelMulZero M₀] : a * b = a ↔ b = 1 ∨ a = 0 := calc
    a * b = a ↔ a * b = a * 1 := by rw [mul_one]
    _ ↔ b = 1 ∨ a = 0 := mul_eq_mul_left_iff

end

section

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem mul_right_surjective₀ {a : G₀} (h : a ≠ 0) : Function.Surjective fun g => g * a := fun g =>
  ⟨g * a⁻¹, by simp [mul_assoc, inv_mul_cancel₀ h]⟩

end

section

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem mul_self_div_self (a : G₀) : a * a / a = a := by rw [div_eq_mul_inv, mul_self_mul_inv a]

end

section

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem mul_self_mul_inv (a : G₀) : a * a * a⁻¹ = a := by
  by_cases h : a = 0
  · rw [h, inv_zero, mul_zero]
  · rw [mul_assoc, mul_inv_cancel₀ h, mul_one]

end

section

variable {M₀ G₀ : Type*}

variable [MulZeroClass M₀] {a b : M₀}

theorem ne_zero_and_ne_zero_of_mul (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 := ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩

end

section

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem ne_zero_of_one_div_ne_zero {a : G₀} (h : 1 / a ≠ 0) : a ≠ 0 := fun ha : a = 0 => by
  rw [ha, div_zero] at h
  contradiction

end

section

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀] {a : M₀} {n : ℕ}

theorem ne_zero_pow (hn : n ≠ 0) (ha : a ^ n ≠ 0) : a ≠ 0 := by rintro rfl; exact ha <| zero_pow hn

end

section

variable {M₀ G₀ : Type*}

variable {R S : Type*} {x y : R}

theorem not_isNilpotent_one [MonoidWithZero R] [Nontrivial R] :
    ¬ IsNilpotent (1 : R) := fun ⟨_, H⟩ ↦ zero_ne_one (H.symm.trans (one_pow _))

end

section

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem one_div_ne_zero {a : G₀} (h : a ≠ 0) : 1 / a ≠ 0 := by
  simpa only [one_div] using inv_ne_zero h

end

section

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀] {a : M₀} {n : ℕ}

theorem pow_mul_eq_zero_of_le {a b : M₀} {m n : ℕ} (hmn : m ≤ n)
    (h : a ^ m * b = 0) : a ^ n * b = 0 := by
  rw [show n = n - m + m by lia, pow_add, mul_assoc, h]
  simp

end

section

variable {M₀ G₀ : Type*}

variable {a b c : M₀}

variable [MulZeroOneClass M₀]

theorem right_eq_mul₀ [IsRightCancelMulZero M₀] (hb : b ≠ 0) : b = a * b ↔ a = 1 := by
  rw [eq_comm, mul_eq_right₀ hb]

end

section

variable {M₀ G₀ : Type*}

variable [MulZeroOneClass M₀] [Nontrivial M₀] {a b : M₀}

theorem right_ne_zero_of_mul_eq_one (h : a * b = 1) : b ≠ 0 := right_ne_zero_of_mul <| ne_zero_of_eq_one h

end

section

variable {M₀ G₀ : Type*}

variable [MulZeroOneClass M₀]

theorem subsingleton_iff_zero_eq_one : (0 : M₀) = 1 ↔ Subsingleton M₀ := ⟨fun h => haveI := uniqueOfZeroEqOne h; inferInstance, fun h => @Subsingleton.elim _ h _ _⟩

alias ⟨subsingleton_of_zero_eq_one, _⟩ := subsingleton_iff_zero_eq_one

end

section

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem zero_eq_inv {a : G₀} : 0 = a⁻¹ ↔ 0 = a := eq_comm.trans <| inv_eq_zero.trans eq_comm

end

section

variable {M₀ G₀ : Type*}

variable [MulZeroOneClass M₀]

theorem zero_ne_one_or_forall_eq_0 : (0 : M₀) ≠ 1 ∨ ∀ a : M₀, a = 0 := not_or_of_imp eq_zero_of_zero_eq_one

end

section

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀] {a : M₀} {n : ℕ}

theorem zero_pow_eq (n : ℕ) : (0 : M₀) ^ n = if n = 0 then 1 else 0 := by
  split_ifs with h
  · rw [h, pow_zero]
  · rw [zero_pow h]

end

section

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀] {a : M₀} {n : ℕ}

theorem zero_pow_eq_one₀ [Nontrivial M₀] : (0 : M₀) ^ n = 1 ↔ n = 0 := by
  rw [zero_pow_eq, one_ne_zero.ite_eq_left_iff]

end

section

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀] {a : M₀} {n : ℕ}

theorem zero_pow_eq_zero [Nontrivial M₀] : (0 : M₀) ^ n = 0 ↔ n ≠ 0 := ⟨by rintro h rfl; simp at h, zero_pow⟩

end

section

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem zero_zpow_eq (n : ℤ) : (0 : G₀) ^ n = if n = 0 then 1 else 0 := by
  split_ifs with h
  · rw [h, zpow_zero]
  · rw [zero_zpow _ h]

end

section

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem zero_zpow_eq_one₀ {n : ℤ} : (0 : G₀) ^ n = 1 ↔ n = 0 := by
  rw [zero_zpow_eq, one_ne_zero.ite_eq_left_iff]

end

section

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem zpow_add' {m n : ℤ} (h : a ≠ 0 ∨ m + n ≠ 0 ∨ m = 0 ∧ n = 0) :
    a ^ (m + n) = a ^ m * a ^ n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  by_cases ha : a = 0
  · subst a
    simp only [false_or, not_true, Ne, hm, hn, false_and, or_false] at h
    rw [zero_zpow _ h, zero_zpow _ hm, zero_mul]
  · exact zpow_add₀ ha m n

end

section

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem zpow_add₀ (ha : a ≠ 0) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => simp
  | succ n ihn => simp only [← Int.add_assoc, zpow_add_one₀ ha, ihn, mul_assoc]
  | pred n ihn => rw [zpow_sub_one₀ ha, ← mul_assoc, ← ihn, ← zpow_sub_one₀ ha, Int.add_sub_assoc]

end

section

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem zpow_sub_one₀ (ha : a ≠ 0) (n : ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ := calc
    a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ ha, mul_one]
    _ = a ^ n * a⁻¹ := by rw [← zpow_add_one₀ ha, Int.sub_add_cancel]

end
