import Mathlib

section

variable {G : Type*}

variable [CommMagma G] {a : G}

theorem CommMagma.IsLeftCancelMul.toIsCancelMul (G : Type u) [CommMagma G] [IsLeftCancelMul G] :
    IsCancelMul G := { CommMagma.IsLeftCancelMul.toIsRightCancelMul G with }

end

section

variable {G : Type*}

variable [CommMagma G] {a : G}

theorem CommMagma.IsLeftCancelMul.toIsRightCancelMul (G : Type u) [CommMagma G] [IsLeftCancelMul G] :
    IsRightCancelMul G := ⟨fun _ _ _ h => mul_left_cancel <| (mul_comm _ _).trans (h.trans (mul_comm _ _))⟩

end

section

variable {G : Type*}

variable [CommMagma G] {a : G}

theorem CommMagma.IsRightCancelMul.toIsCancelMul (G : Type u) [CommMagma G] [IsRightCancelMul G] :
    IsCancelMul G := { CommMagma.IsRightCancelMul.toIsLeftCancelMul G with }

end

section

variable {G : Type*}

variable [CommMagma G] {a : G}

theorem CommMagma.IsRightCancelMul.toIsLeftCancelMul (G : Type u) [CommMagma G] [IsRightCancelMul G] :
    IsLeftCancelMul G := ⟨fun _ _ _ h => mul_right_cancel <| (mul_comm _ _).trans (h.trans (mul_comm _ _))⟩

end

section

variable {G : Type*}

theorem MulOneClass.ext {M : Type u} : ∀ ⦃m₁ m₂ : MulOneClass M⦄, m₁.mul = m₂.mul → m₁ = m₂ := by
  rintro @⟨@⟨⟨one₁⟩, ⟨mul₁⟩⟩, one_mul₁, mul_one₁⟩ @⟨@⟨⟨one₂⟩, ⟨mul₂⟩⟩, one_mul₂, mul_one₂⟩ ⟨rfl⟩
  -- FIXME (See https://github.com/leanprover/lean4/issues/1711)
  -- congr
  suffices one₁ = one₂ by cases this; rfl
  exact (one_mul₂ one₁).symm.trans (mul_one₁ one₂)

end

section

variable {G : Type*}

variable [DivInvMonoid G]

theorem div_eq_mul_inv (a b : G) : a / b = a * b⁻¹ := DivInvMonoid.div_eq_mul_inv _ _

alias division_def := div_eq_mul_inv

end

section

variable {G : Type*}

variable [Group G] {a b : G}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := left_inv_eq_right_inv (inv_mul_cancel a) h


theorem div_mul_cancel (a b : G) : a / b * b = a := by
  rw [div_eq_mul_inv, inv_mul_cancel_right a b]

end

section

variable {G : Type*}

variable [Group G] {a b : G}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := left_inv_eq_right_inv (inv_mul_cancel a) h


theorem div_self' (a : G) : a / a = 1 := by rw [div_eq_mul_inv, mul_inv_cancel a]

end

section

variable {G : Type*}

variable [DivisionMonoid G] {a b : G}

theorem inv_eq_of_mul_eq_one_left (h : a * b = 1) : b⁻¹ = a := by
  rw [← inv_eq_of_mul_eq_one_right h, inv_inv]

end

section

variable {G : Type*}

variable [Group G] {a b : G}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := left_inv_eq_right_inv (inv_mul_cancel a) h


theorem inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b := by
  rw [← mul_assoc, inv_mul_cancel, one_mul]

end

section

variable {G : Type*}

variable [Group G] {a b : G}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := left_inv_eq_right_inv (inv_mul_cancel a) h


theorem inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a := by
  rw [mul_assoc, inv_mul_cancel, mul_one]

end

section

variable {G : Type*}

variable [CommMagma G] {a : G}

theorem isLeftRegular_iff_isRegular : IsLeftRegular a ↔ IsRegular a := by
  simp [isRegular_iff, IsLeftRegular, IsRightRegular, mul_comm]

end

section

variable {G : Type*}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := left_inv_eq_right_inv (inv_mul_cancel a) h


theorem isMulCommutative_iff {M : Type*} [Mul M] :
    IsMulCommutative M ↔ ∀ a b : M, a * b = b * a := by
  grind [IsMulCommutative, Std.Commutative]

end

section

variable {G : Type*}

variable [CommMagma G] {a : G}

theorem isRightRegular_iff_isRegular : IsRightRegular a ↔ IsRegular a := by
  simp [isRegular_iff, IsLeftRegular, IsRightRegular, mul_comm]

end

section

variable {G : Type*}

variable [DivInvMonoid G]

theorem mul_div_assoc (a b c : G) : a * b / c = a * (b / c) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc _ _ _]

end

section

variable {G : Type*}

variable [Group G] {a b : G}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := left_inv_eq_right_inv (inv_mul_cancel a) h


theorem mul_div_cancel_right (a b : G) : a * b / b = a := by
  rw [div_eq_mul_inv, mul_inv_cancel_right a b]

end

section

variable {G : Type*}

variable [Group G] {a b : G}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := left_inv_eq_right_inv (inv_mul_cancel a) h


set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  rw [← inv_mul_cancel a⁻¹, inv_eq_of_mul (inv_mul_cancel a)]

end

section

variable {G : Type*}

variable [CommGroup G]

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := left_inv_eq_right_inv (inv_mul_cancel a) h


set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem mul_inv_cancel_comm (a b : G) : a * b * a⁻¹ = b := by rw [mul_comm, inv_mul_cancel_left]

end

section

variable {G : Type*}

variable [Group G] {a b : G}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := left_inv_eq_right_inv (inv_mul_cancel a) h


theorem mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b := by
  rw [← mul_assoc, mul_inv_cancel, one_mul]

end

section

variable {G : Type*}

variable [Group G] {a b : G}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := left_inv_eq_right_inv (inv_mul_cancel a) h


theorem mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a := by
  rw [mul_assoc, mul_inv_cancel, mul_one]

end

section

variable {G : Type*}

variable [Mul G]

variable [IsLeftCancelMul G] {a b c : G}

theorem mul_left_cancel : a * b = a * c → b = c := (IsLeftCancelMul.mul_left_cancel a ·)

end

section

variable {G : Type*}

variable [Mul G]

variable [IsRightCancelMul G] {a b c : G}

theorem mul_right_cancel : a * b = c * b → a = c := (IsRightCancelMul.mul_right_cancel b ·)

end

section

variable {G : Type*}

variable [Mul G]

variable [IsRightCancelMul G] {a b c : G}

theorem mul_right_cancel_iff : b * a = c * a ↔ b = c := ⟨mul_right_cancel, congrArg (· * a)⟩

end

section

variable {G : Type*}

variable [DivInvMonoid G]

theorem negSucc_zsmul {G} [SubNegMonoid G] (a : G) (n : ℕ) :
    Int.negSucc n • a = -((n + 1) • a) := by
  rw [← natCast_zsmul]
  exact SubNegMonoid.zsmul_neg' n a

attribute [to_additive existing (attr := simp) negSucc_zsmul] zpow_negSucc

end

section

variable {G : Type*}

theorem npowBinRec.go_spec {M : Type*} [Semigroup M] [One M] (k : ℕ) (m n : M) :
    npowBinRec.go (k + 1) m n = m * npowRec' (k + 1) n := by
  unfold go
  generalize hk : k + 1 = k'
  replace hk : k' ≠ 0 := by lia
  induction k' using Nat.binaryRecFromOne generalizing n m with
  | zero => simp at hk
  | one => simp [npowRec']
  | bit b k' k'0 ih =>
    rw [Nat.binaryRec_eq _ _ (Or.inl rfl), ih _ _ k'0]
    cases b <;> simp only [Nat.bit, cond_false, cond_true, npowRec'_two_mul]
    rw [npowRec'_succ (by lia), npowRec'_two_mul, ← npowRec'_two_mul,
      ← npowRec'_mul_comm (by lia), mul_assoc]

end

section

variable {G : Type*}

theorem npowRec'_mul_comm {M : Type*} [Semigroup M] [One M] {k : ℕ} (k0 : k ≠ 0) (m : M) :
    m * npowRec' k m = npowRec' k m * m := by
  induction k using Nat.strongRecOn with
  | ind k' ih =>
    match k' with
    | 1 => simp [npowRec']
    | k + 2 => simp [npowRec', ← mul_assoc, ih]

end

section

variable {G : Type*}

theorem npowRec'_two_mul {M : Type*} [Semigroup M] [One M] (k : ℕ) (m : M) :
    npowRec' (2 * k) m = npowRec' k (m * m) := by
  induction k using Nat.strongRecOn with
  | ind k' ih =>
    match k' with
    | 0 => rfl
    | 1 => simp [npowRec']
    | k + 2 => simp [npowRec', ← mul_assoc, ← ih]

end

section

variable {G : Type*}

theorem npowRec_eq {M : Type*} [Semigroup M] [One M] (k : ℕ) (m : M) :
    npowRec (k + 1) m = 1 * npowRec' (k + 1) m := by
  induction k using Nat.strongRecOn with
  | ind k' ih =>
    match k' with
    | 0 => rfl
    | k + 1 =>
      rw [npowRec, npowRec'_succ k.succ_ne_zero, ← mul_assoc]
      congr
      simp [ih]

end

section

variable {G : Type*}

theorem npowRec_eq_npowBinRec : @npowRecAuto = @npowBinRecAuto := by
  funext M _ _ k m
  rw [npowBinRecAuto, npowRecAuto, npowBinRec]
  match k with
  | 0 => rw [npowRec, npowBinRec.go, Nat.binaryRec_zero]
  | k + 1 => rw [npowBinRec.go_spec, npowRec_eq]

end

section

variable {G : Type*}

variable {M : Type*} [Monoid M] {a b c : M}

theorem pow_one (a : M) : a ^ 1 = a := by rw [pow_succ, pow_zero, one_mul]

end

section

variable {G : Type*}

variable {M : Type*} [Monoid M] {a b c : M}

theorem pow_right_comm (a : M) (m n : ℕ) : (a ^ m) ^ n = (a ^ n) ^ m := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]

end

section

variable {G : Type*}

variable {M : Type*} [Monoid M] {a b c : M}

theorem pow_three (a : M) : a ^ 3 = a * (a * a) := by rw [pow_succ', pow_two]

-- This lemma is higher priority than later `smul_zero` so that the `simpNF` is happy

end

section

variable {G : Type*}

variable [DivInvMonoid G]

theorem zpow_natCast (a : G) : ∀ n : ℕ, a ^ (n : ℤ) = a ^ n
  | 0 => (zpow_zero _).trans (pow_zero _).symm
  | n + 1 => calc
    a ^ (↑(n + 1) : ℤ) = a ^ (n : ℤ) * a := DivInvMonoid.zpow_succ' _ _
    _ = a ^ n * a := congrArg (· * a) (zpow_natCast a n)
    _ = a ^ (n + 1) := (pow_succ _ _).symm

end

section

variable {G : Type*}

variable [DivInvMonoid G]

theorem zpow_negSucc (a : G) (n : ℕ) : a ^ (Int.negSucc n) = (a ^ (n + 1))⁻¹ := by
  rw [← zpow_natCast]
  exact DivInvMonoid.zpow_neg' n a

end

section

variable {G : Type*}

variable [DivInvMonoid G]

theorem zpow_neg_one (x : G) : x ^ (-1 : ℤ) = x⁻¹ := (zpow_negSucc x 0).trans <| congr_arg Inv.inv (pow_one x)

end
