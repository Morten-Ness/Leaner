import Mathlib

section

variable {α : Type*}

variable [Semigroup α] {a b c : α}

theorem Dvd.elim {P : Prop} {a b : α} (H₁ : a ∣ b) (H₂ : ∀ c, b = a * c → P) : P := Exists.elim H₁ H₂

attribute [local simp] mul_assoc mul_comm mul_left_comm

end

section

variable {α : Type*}

variable [CommSemigroup α] {a b c : α}

theorem Dvd.elim_left {P : Prop} (h₁ : a ∣ b) (h₂ : ∀ c, b = c * a → P) : P := Exists.elim (exists_eq_mul_left_of_dvd h₁) fun c => fun h₃ : b = c * a => h₂ c h₃

end

section

variable {α : Type*}

variable [Semigroup α] {a b c : α}

theorem Dvd.intro (c : α) (h : a * c = b) : a ∣ b := Exists.intro c h.symm

alias dvd_of_mul_right_eq := Dvd.intro

end

section

variable {α : Type*}

variable [CommSemigroup α] {a b c : α}

theorem Dvd.intro_left (c : α) (h : c * a = b) : a ∣ b := Dvd.intro c (by rw [mul_comm] at h; apply h)

alias dvd_of_mul_left_eq := Dvd.intro_left

end

section

variable {α : Type*}

variable [Semigroup α] {a b c : α}

theorem IsLeftRegular.dvd_cancel_left (h : IsLeftRegular a) : a * b ∣ a * c ↔ b ∣ c := ⟨fun dvd ↦ have ⟨d, eq⟩ := dvd; ⟨d, h (eq.trans <| mul_assoc ..)⟩, mul_dvd_mul_left a⟩

end

section

variable {α : Type*}

variable [Semigroup α] {a b c : α}

theorem dvd_def : a ∣ b ↔ ∃ c, b = a * c := Iff.rfl

alias dvd_iff_exists_eq_mul_right := dvd_def

end

section

variable {α : Type*}

variable [CommSemigroup α] {a b c : α}

theorem dvd_iff_exists_eq_mul_left : a ∣ b ↔ ∃ c, b = c * a := ⟨exists_eq_mul_left_of_dvd, by
    rintro ⟨c, rfl⟩
    exact ⟨c, mul_comm _ _⟩⟩

end

section

variable {α : Type*}

variable [CommSemigroup α] {a b c : α}

theorem dvd_mul [DecompositionMonoid α] {k m n : α} :
    k ∣ m * n ↔ ∃ d₁ d₂, d₁ ∣ m ∧ d₂ ∣ n ∧ k = d₁ * d₂ := by
  refine ⟨exists_dvd_and_dvd_of_dvd_mul, ?_⟩
  rintro ⟨d₁, d₂, hy, hz, rfl⟩
  gcongr

end

section

variable {α : Type*}

variable [Semigroup α] {a b c : α}

theorem dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c := h.trans (dvd_mul_right b c)

alias Dvd.dvd.mul_right := dvd_mul_of_dvd_left

end

section

variable {α : Type*}

variable [CommSemigroup α] {a b c : α}

theorem dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c * b := by
  rw [mul_comm]; exact h.mul_right _

alias Dvd.dvd.mul_left := dvd_mul_of_dvd_right

attribute [local simp] mul_assoc mul_comm mul_left_comm

end

section

variable {α : Type*}

variable [Monoid α] {a b c : α} {m n : ℕ}

theorem dvd_of_eq (h : a = b) : a ∣ b := by rw [h]

alias Eq.dvd := dvd_of_eq

end

section

variable {α : Type*}

variable [CommSemigroup α] {a b c : α}

theorem dvd_of_mul_left_dvd (h : a * b ∣ c) : b ∣ c := Dvd.elim h fun d ceq => Dvd.intro (a * d) (by simp [ceq])

end

section

variable {α : Type*}

variable [CommSemigroup α] {a b c : α}

theorem exists_eq_mul_left_of_dvd (h : a ∣ b) : ∃ c, b = c * a := Dvd.elim h fun c => fun H1 : b = a * c => Exists.intro c (Eq.trans H1 (mul_comm a c))

end

section

variable {α : Type*}

variable [Semigroup α] {a b c : α}

theorem mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c := by
  obtain ⟨d, rfl⟩ := h
  use d
  rw [mul_assoc]

end

section

variable {α : Type*}

variable [Monoid α] {a b c : α} {m n : ℕ}

theorem pow_dvd_pow (a : α) (h : m ≤ n) : a ^ m ∣ a ^ n := ⟨a ^ (n - m), by rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel h]⟩

end

section

variable {α : Type*}

variable [CommMonoid α] {a b : α}

theorem pow_dvd_pow_of_dvd (h : a ∣ b) (n : ℕ) : a ^ n ∣ b ^ n := by
  induction n with
  | zero => simp
  | succ =>
    rw [pow_succ, pow_succ]
    gcongr

end

section

variable {α : Type*}

variable [CommMonoid α] {a b : α}

theorem pow_dvd_pow_of_dvd_of_le {m n : ℕ} (hab : a ∣ b) (hmn : m ≤ n) : a ^ m ∣ b ^ n := by
  trans (a ^ n) <;> [gcongr; apply_rules [pow_dvd_pow_of_dvd]]

end
