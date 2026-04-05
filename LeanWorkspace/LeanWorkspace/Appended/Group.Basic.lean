import Mathlib

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem conj_eq_one_iff : a * b * a⁻¹ = 1 ↔ b = 1 := by
  rw [mul_inv_eq_one, mul_eq_left]

end

section

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem div_div_div_cancel_left (a b c : G) : c / a / (c / b) = b / a := by
  rw [← inv_div b c, div_inv_eq_mul, mul_comm, div_mul_div_cancel]

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem div_div_div_cancel_right (a b c : G) : a / c / (b / c) = a / b := by
  rw [← inv_div c b, div_inv_eq_mul, div_mul_div_cancel]

end

section

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem div_eq_div_iff_comm : a / b = c / d ↔ b / a = d / c := inv_inj.symm.trans <| by simp only [inv_div]

end

section

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem div_eq_div_iff_div_eq_div : a / b = c / d ↔ a / c = b / d := by
  rw [div_eq_iff_eq_mul, div_mul_eq_mul_div, div_eq_iff_eq_mul', mul_div_assoc]

end

section

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem div_eq_div_iff_mul_eq_mul : a / b = c / d ↔ a * d = c * b := by
  rw [div_eq_iff_eq_mul, div_mul_eq_mul_div, eq_comm, div_eq_iff_eq_mul']
  simp only [mul_comm, eq_comm]

end

section

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem div_eq_iff_comm : a / b = c ↔ a / c = b := by rw [div_eq_iff_eq_mul', div_eq_iff_eq_mul]

end

section

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem div_eq_iff_eq_mul' : a / b = c ↔ a = b * c := by rw [div_eq_iff_eq_mul, mul_comm]

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem div_eq_iff_eq_mul : a / b = c ↔ a = c * b := by rw [div_eq_mul_inv, mul_inv_eq_iff_eq_mul]

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem div_eq_inv_self : a / b = b⁻¹ ↔ a = 1 := by rw [div_eq_mul_inv, mul_eq_right]

end

section

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem div_eq_of_eq_mul' {a b c : G} (h : a = b * c) : a / b = c := by
  rw [h, div_eq_mul_inv, mul_comm, inv_mul_cancel_left]

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem div_eq_one : a / b = 1 ↔ a = b := ⟨eq_of_div_eq_one, fun h ↦ by rw [h, div_self']⟩

alias ⟨_, div_eq_one_of_eq⟩ := div_eq_one

alias ⟨_, sub_eq_zero_of_eq⟩ := sub_eq_zero

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem div_eq_self : a / b = a ↔ b = 1 := by rw [div_eq_mul_inv, mul_eq_left, inv_eq_one]

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem div_left_inj : b / a = c / a ↔ b = c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_left_inj _

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem div_left_injective : Function.Injective fun a ↦ a / b := by
  -- FIXME this could be by `simpa`, but it fails. This is probably a bug in `simpa`.
  simp only [div_eq_mul_inv]
  exact fun a a' h ↦ mul_left_injective b⁻¹ h

end

section

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem div_mul_cancel_left (a b : G) : a / (a * b) = b⁻¹ := by rw [← inv_div, mul_div_cancel_left]

-- This lemma is in the `simp` set under the name `mul_inv_cancel_comm_assoc`,
-- along with the additive version `add_neg_cancel_comm_assoc`,
-- defined in `Algebra.Group.Commute`

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem div_mul_cancel_right (a b : G) : a / (b * a) = b⁻¹ := by rw [← inv_div, mul_div_cancel_right]

end

section

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem div_mul_div_cancel' (a b c : G) : a / b * (c / a) = c / b := by
  rw [mul_comm]; apply div_mul_div_cancel

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem div_mul_div_cancel (a b c : G) : a / b * (b / c) = a / c := by
  rw [← mul_div_assoc, div_mul_cancel]

end

section

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem div_mul_eq_div_div_swap : a / (b * c) = a / c / b := by
  simp only [mul_assoc, mul_inv_rev, div_eq_mul_inv]

end

section

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem div_mul_mul_cancel (a b c : G) : a / c * (b * c) = a * b := by
  rw [mul_left_comm, div_mul_cancel, mul_comm]

end

section

variable {α β G M : Type*}

variable [DivisionCommMonoid α] (a b c d : α)

theorem div_pow (a b : α) (n : ℕ) : (a / b) ^ n = a ^ n / b ^ n := by
  simp only [div_eq_mul_inv, mul_pow, inv_pow]

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem div_right_injective : Function.Injective fun a ↦ b / a := by
  -- FIXME see above
  simp only [div_eq_mul_inv]
  exact fun a a' h ↦ inv_injective (mul_right_injective b h)

end

section

variable {α β G M : Type*}

variable [DivisionCommMonoid α] (a b c d : α)

theorem div_zpow (a b : α) (n : ℤ) : (a / b) ^ n = a ^ n / b ^ n := by
  simp only [div_eq_mul_inv, mul_zpow, inv_zpow]

end

section

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem eq_div_iff_mul_eq'' : a = b / c ↔ c * a = b := by rw [eq_div_iff_mul_eq', mul_comm]

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem eq_div_iff_mul_eq' : a = b / c ↔ a * c = b := by rw [div_eq_mul_inv, eq_mul_inv_iff_mul_eq]

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem eq_iff_eq_of_div_eq_div (H : a / b = c / d) : a = b ↔ c = d := by
  rw [← div_eq_one, H, div_eq_one]

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c := ⟨fun h ↦ by rw [h, mul_inv_cancel_left], fun h ↦ by rw [← h, inv_mul_cancel_left]⟩

end

section

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem eq_inv_of_mul_eq_one_right (h : a * b = 1) : b = a⁻¹ := (inv_eq_of_mul_eq_one_right h).symm

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b := ⟨fun h ↦ by rw [h, inv_mul_cancel_right], fun h ↦ by rw [← h, mul_inv_cancel_right]⟩

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem eq_mul_of_inv_mul_eq (h : b⁻¹ * a = c) : a = b * c := by simp [h.symm, mul_inv_cancel_left]

end

section

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem eq_of_div_eq_one (h : a / b = 1) : a = b := inv_injective <| inv_eq_of_mul_eq_one_right <| by rwa [← div_eq_mul_inv]

end

section

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem eq_of_inv_mul_eq_one (h : a⁻¹ * b = 1) : a = b := by simpa using eq_inv_of_mul_eq_one_left h

end

section

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem eq_of_mul_inv_eq_one (h : a * b⁻¹ = 1) : a = b := by simpa using eq_inv_of_mul_eq_one_left h

end

section

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem eq_of_one_div_eq_one_div (h : 1 / a = 1 / b) : a = b := by
  rw [← one_div_one_div a, h, one_div_one_div]

-- Note that `mul_zsmul` and `zpow_mul` have the primes swapped
-- when additivised since their argument order,
-- and therefore the more "natural" choice of lemma, is reversed.

end

section

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem eq_one_div_of_mul_eq_one_left (h : b * a = 1) : b = 1 / a := by
  rw [eq_inv_of_mul_eq_one_left h, one_div]

end

section

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem eq_one_div_of_mul_eq_one_right (h : a * b = 1) : b = 1 / a := by
  rw [eq_inv_of_mul_eq_one_right h, one_div]

end

section

variable {α β G M : Type*}

variable [MulOneClass M]

theorem eq_one_iff_eq_one_of_mul_eq_one {a b : M} (h : a * b = 1) : a = 1 ↔ b = 1 := by
  constructor <;> (rintro rfl; simpa using h)

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem inv_mul_eq_iff_eq_mul : a⁻¹ * b = c ↔ b = a * c := ⟨fun h ↦ by rw [← h, mul_inv_cancel_left], fun h ↦ by rw [h, inv_mul_cancel_left]⟩

end

section

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem inv_mul_eq_inv_mul_iff_mul_eq_mul : b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b := by
  rw [← div_eq_inv_mul, ← div_eq_inv_mul, div_eq_div_iff_mul_eq_mul]

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b := by rw [mul_eq_one_iff_eq_inv, inv_inj]

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem inv_pow_sub (a : G) {m n : ℕ} (h : n ≤ m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n := by
  rw [pow_sub a⁻¹ h, inv_pow, inv_pow, inv_inv]

end

section

variable {α β G M : Type*}

variable [CommMonoid M] {x y z : M}

theorem inv_unique (hy : x * y = 1) (hz : x * z = 1) : y = z := left_inv_eq_right_inv (Trans.trans (mul_comm _ _) hy) hz

end

section

variable {α β G M : Type*}

variable [DivInvMonoid G]

theorem mul_div (a b c : G) : a * (b / c) = a * b / c := by simp only [mul_assoc, div_eq_mul_inv]

end

section

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem mul_div_cancel (a b : G) : a * (b / a) = b := by
  rw [← mul_div_assoc, mul_div_cancel_left]

end

section

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem mul_div_cancel_left (a b : G) : a * b / a = b := by rw [div_eq_inv_mul, inv_mul_cancel_left]

end

section

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem mul_div_div_cancel (a b c : G) : a * b / (a / c) = b * c := by
  rw [← div_mul, mul_div_cancel_left]

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem mul_div_mul_right_eq_div (a b c : G) : a * c / (b * c) = a / b := by
  rw [div_mul_eq_div_div_swap]; simp only [mul_div_cancel_right]

end

section

variable {α β G M : Type*}

variable [Monoid M] [IsLeftCancelMul M] {a b : M}

theorem mul_eq_left : a * b = a ↔ b = 1 := calc
  a * b = a ↔ a * b = a * 1 := by rw [mul_one]
  _ ↔ b = 1 := mul_left_cancel_iff

end

section

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem mul_eq_of_eq_div' (h : b = c / a) : a * b = c := by
  rw [h, div_eq_mul_inv, mul_comm c, mul_inv_cancel_left]

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem mul_eq_one_iff_eq_inv' : a * b = 1 ↔ b = a⁻¹ := by
  rw [mul_eq_one_iff_inv_eq, eq_comm]

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹ := ⟨eq_inv_of_mul_eq_one_left, fun h ↦ by rw [h, inv_mul_cancel]⟩

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem mul_eq_one_iff_inv_eq' : a * b = 1 ↔ b⁻¹ = a := by
  rw [mul_eq_one_iff_eq_inv, eq_comm]

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem mul_eq_one_iff_inv_eq : a * b = 1 ↔ a⁻¹ = b := by
  rw [mul_eq_one_iff_eq_inv, inv_eq_iff_eq_inv]

end

section

variable {α β G M : Type*}

variable [Monoid M] [IsRightCancelMul M] {a b : M}

theorem mul_eq_right : a * b = b ↔ a = 1 := calc
  a * b = b ↔ a * b = 1 * b := by rw [one_mul]
  _ ↔ a = 1 := mul_right_cancel_iff

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b := ⟨fun h ↦ by rw [← h, inv_mul_cancel_right], fun h ↦ by rw [h, mul_inv_cancel_right]⟩

end

section

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem mul_inv_eq_mul_inv_iff_mul_eq_mul : a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b := by
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b := by rw [mul_eq_one_iff_eq_inv, inv_inv]

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem mul_inv_mul_mul_cancel (a b c : G) : a * b⁻¹ * (b * c) = a * c := by
  rw [mul_assoc, ← mul_assoc b⁻¹, inv_mul_cancel, one_mul]

end

section

variable {α β G M : Type*}

variable [CommSemigroup G]

theorem mul_left_comm (a b c : G) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, mul_comm a, mul_assoc]

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem mul_left_surjective (a : G) : Function.Surjective (a * ·) := fun x ↦ ⟨a⁻¹ * x, mul_inv_cancel_left a x⟩

end

section

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem mul_mul_div_cancel (a b c : G) : a * c * (b / c) = a * b := by
  rw [mul_assoc, mul_div_cancel]

end

section

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem mul_mul_inv_cancel'_right (a b : G) : a * (b * a⁻¹) = b := by
  rw [← div_eq_mul_inv, mul_div_cancel a b]

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem mul_mul_inv_mul_cancel (a b c : G) : a * b * (b⁻¹ * c) = a * c := by
  rw [mul_assoc, ← mul_assoc b, mul_inv_cancel, one_mul]

end

section

variable {α β G M : Type*}

variable [CommSemigroup G]

theorem mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a * c * (b * d) := by
  simp only [mul_left_comm, mul_assoc]

end

section

variable {α β G M : Type*}

variable [DivInvMonoid G]

theorem mul_one_div (x y : G) : x * (1 / y) = x / y := by
  rw [div_eq_mul_inv, one_mul, div_eq_mul_inv]

end

section

variable {α β G M : Type*}

variable [Monoid M] {a b : M} {m n : ℕ}

theorem mul_pow_sub_one (hn : n ≠ 0) (a : M) : a * a ^ (n - 1) = a ^ n := by
  rw [← pow_succ', Nat.sub_add_cancel <| Nat.one_le_iff_ne_zero.2 hn]

end

section

variable {α β G M : Type*}

variable [CommSemigroup G]

theorem mul_right_comm (a b c : G) : a * b * c = a * c * b := by
  rw [mul_assoc, mul_comm b, mul_assoc]

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem mul_right_surjective (a : G) : Function.Surjective fun x ↦ x * a := fun x ↦
  ⟨x * a⁻¹, inv_mul_cancel_right x a⟩

end

section

variable {α β G M : Type*}

variable [CommSemigroup G]

theorem mul_rotate' (a b c : G) : a * (b * c) = b * (c * a) := by
  simp only [mul_left_comm, mul_comm]

end

section

variable {α β G M : Type*}

variable [CommSemigroup G]

theorem mul_rotate (a b c : G) : a * b * c = b * c * a := by
  simp only [mul_left_comm, mul_comm]

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem mul_self_zpow (a : G) (n : ℤ) : a * a ^ n = a ^ (n + 1) := by
  rw [Int.add_comm, zpow_add, zpow_one]

end

section

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem mul_zpow_neg_one (a b : α) : (a * b) ^ (-1 : ℤ) = b ^ (-1 : ℤ) * a ^ (-1 : ℤ) := by
  simp only [zpow_neg, zpow_one, mul_inv_rev]

end

section

variable {α β G M : Type*}

variable [Monoid β] (p r : α → α → Prop) [Std.Total r] (f : α → α → β)

theorem multiplicative_of_symmetric_of_total
    (hsymm : Symmetric p) (hf_swap : ∀ {a b}, p a b → f a b * f b a = 1)
    (hmul : ∀ {a b c}, r a b → r b c → p a b → p b c → p a c → f a c = f a b * f b c)
    {a b c : α} (pab : p a b) (pbc : p b c) (pac : p a c) : f a c = f a b * f b c := by
  have hmul' : ∀ {b c}, r b c → p a b → p b c → p a c → f a c = f a b * f b c := by
    intro b c rbc pab pbc pac
    obtain rab | rba := total_of r a b
    · exact hmul rab rbc pab pbc pac
    rw [← one_mul (f a c), ← hf_swap pab, mul_assoc]
    obtain rac | rca := total_of r a c
    · rw [hmul rba rac (hsymm pab) pac pbc]
    · rw [hmul rbc rca pbc (hsymm pac) (hsymm pab), mul_assoc, hf_swap (hsymm pac), mul_one]
  obtain rbc | rcb := total_of r b c
  · exact hmul' rbc pab pbc pac
  · rw [hmul' rcb pac (hsymm pbc) pab, mul_assoc, hf_swap (hsymm pbc), mul_one]

end

section

variable {α β G M : Type*}

variable [Monoid β] (p r : α → α → Prop) [Std.Total r] (f : α → α → β)

theorem multiplicative_of_total (p : α → Prop) (hswap : ∀ {a b}, p a → p b → f a b * f b a = 1)
    (hmul : ∀ {a b c}, r a b → r b c → p a → p b → p c → f a c = f a b * f b c) {a b c : α}
    (pa : p a) (pb : p b) (pc : p c) : f a c = f a b * f b c := by
  apply multiplicative_of_symmetric_of_total (fun a b => p a ∧ p b) r f fun _ _ => And.symm
  · simp_rw [and_imp]; exact @hswap
  · exact fun rab rbc pab _pbc pac => hmul rab rbc pab.1 pab.2 pac.2
  exacts [⟨pa, pb⟩, ⟨pb, pc⟩, ⟨pa, pc⟩]

end

section

variable {α β G M : Type*}

variable [Monoid M] {a b : M} {m n : ℕ}

theorem pow_boole (P : Prop) [Decidable P] (a : M) :
    (a ^ if P then 1 else 0) = if P then a else 1 := by simp only [pow_ite, pow_one, pow_zero]

end

section

variable {α β G M : Type*}

variable [Monoid M] {a b : M} {m n : ℕ}

theorem pow_eq_pow_mod (m : ℕ) (ha : a ^ n = 1) : a ^ m = a ^ (m % n) := by
  calc
    a ^ m = a ^ (m % n + n * (m / n)) := by rw [Nat.mod_add_div]
    _ = a ^ (m % n) := by simp [pow_add, pow_mul, ha]

end

section

variable {α β G M : Type*}

variable [Monoid M] {a b : M} {m n : ℕ}

theorem pow_mul_pow_sub (a : M) (h : m ≤ n) : a ^ m * a ^ (n - m) = a ^ n := by
  rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel h]

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem pow_sub (a : G) {m n : ℕ} (h : n ≤ m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := eq_mul_inv_of_mul_eq <| by rw [← pow_add, Nat.sub_add_cancel h]

end

section

variable {α β G M : Type*}

variable [Monoid M] {a b : M} {m n : ℕ}

theorem pow_sub_mul_pow (a : M) (h : m ≤ n) : a ^ (n - m) * a ^ m = a ^ n := by
  rw [← pow_add, Nat.sub_add_cancel h]

end

section

variable {α β G M : Type*}

variable [Monoid M] {a b : M} {m n : ℕ}

theorem pow_sub_one_mul (hn : n ≠ 0) (a : M) : a ^ (n - 1) * a = a ^ n := by
  rw [← pow_succ, Nat.sub_add_cancel <| Nat.one_le_iff_ne_zero.2 hn]

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem zpow_add (a : G) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => simp
  | succ n ihn => simp only [← Int.add_assoc, zpow_add_one, ihn, mul_assoc]
  | pred n ihn => rw [zpow_sub_one, ← mul_assoc, ← ihn, ← zpow_sub_one, Int.add_sub_assoc]

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem zpow_eq_zpow_emod {x : G} (m : ℤ) {n : ℤ} (h : x ^ n = 1) :
    x ^ m = x ^ (m % n) := calc
    x ^ m = x ^ (m % n + n * (m / n)) := by rw [Int.emod_add_mul_ediv]
    _ = x ^ (m % n) := by simp [zpow_add, zpow_mul, h]

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem zpow_induction_left {g : G} {P : G → Prop} (h_one : P (1 : G))
    (h_mul : ∀ a, P a → P (g * a)) (h_inv : ∀ a, P a → P (g⁻¹ * a)) (n : ℤ) : P (g ^ n) := by
  induction n with
  | zero => rwa [zpow_zero]
  | succ n ih =>
    rw [Int.add_comm, zpow_add, zpow_one]
    exact h_mul _ ih
  | pred n ih =>
    rw [Int.sub_eq_add_neg, Int.add_comm, zpow_add, zpow_neg_one]
    exact h_inv _ ih

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem zpow_induction_right {g : G} {P : G → Prop} (h_one : P (1 : G))
    (h_mul : ∀ a, P a → P (a * g)) (h_inv : ∀ a, P a → P (a * g⁻¹)) (n : ℤ) : P (g ^ n) := by
  induction n with
  | zero => rwa [zpow_zero]
  | succ n ih =>
    rw [zpow_add_one]
    exact h_mul _ ih
  | pred n ih =>
    rw [zpow_sub_one]
    exact h_inv _ ih

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem zpow_natCast_sub_natCast (a : G) (m n : ℕ) : a ^ (m - n : ℤ) = a ^ m / a ^ n := by
  simpa [div_eq_mul_inv] using zpow_sub a m n

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem zpow_natCast_sub_one (a : G) (n : ℕ) : a ^ (n - 1 : ℤ) = a ^ n / a := by
  simpa [div_eq_mul_inv] using zpow_sub a n 1

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem zpow_one_sub_natCast (a : G) (n : ℕ) : a ^ (1 - n : ℤ) = a / a ^ n := by
  simpa [div_eq_mul_inv] using zpow_sub a 1 n

end

section

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem zpow_sub_one (a : G) (n : ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ := calc
    a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ := (mul_inv_cancel_right _ _).symm
    _ = a ^ n * a⁻¹ := by rw [← zpow_add_one, Int.sub_add_cancel]

end
