import Mathlib

section

variable {F α β : Type*}

theorem Even.isSquare_zpow [Group α] {n : ℤ} : Even n → ∀ a : α, IsSquare (a ^ n) := by
  aesop (add simp zpow_add)

example {G : Type*} [CommGroup G] {a b c d e : G} (ha : IsSquare a) {n : ℕ} {k : ℤ} (hk : Even k) :
    IsSquare <| a * (b * b) / (c ^ 2) * (d ^ k) * (e ^ (n + n)) := by aesop

example {G : Type*} [AddCommGroup G] {a b c d e : G} (ha : Even a) {n : ℕ} {k : ℤ} (hk : Even k) :
    Even <| a + (b + b) - 2 • c + k • d + (n + n) • e := by aesop

end

section

variable {F α β : Type*}

theorem IsSquare.mul [CommSemigroup α] {a b : α} : IsSquare a → IsSquare b → IsSquare (a * b) := fun ⟨r, _⟩ ⟨s, _⟩ => ⟨r * s, by simp_all [mul_mul_mul_comm]⟩

end

section

variable {F α β : Type*}

theorem IsSquare.one [MulOneClass α] : IsSquare (1 : α) := ⟨1, (mul_one _).symm⟩

grind_pattern IsSquare.one => IsSquare (1 : α)
grind_pattern Even.zero => Even (0 : α)

end

section

variable {F α β : Type*}

variable [Monoid α] {n : ℕ} {a : α}

theorem IsSquare.pow (n : ℕ) (ha : IsSquare a) : IsSquare (a ^ n) := by
  aesop (add simp Commute.mul_pow)

end

section

variable {F α β : Type*}

variable [DivisionMonoid α] {a : α}

theorem IsSquare.zpow (n : ℤ) : IsSquare a → IsSquare (a ^ n) := by
  aesop (add simp Commute.mul_zpow)

end

section

variable {F α β : Type*}

variable [Mul α]

theorem isSquare_iff_exists_mul_self (a : α) : IsSquare a ↔ ∃ r, a = r * r := .rfl

alias ⟨IsSquare.exists_mul_self, _⟩ := isSquare_iff_exists_mul_self
attribute [to_additive (attr := aesop unsafe 5% forward)] IsSquare.exists_mul_self

end

section

variable {F α β : Type*}

variable [Mul α]

theorem isSquare_op_iff {a : α} : IsSquare (op a) ↔ IsSquare a := ⟨fun ⟨r, hr⟩ ↦ ⟨unop r, congr_arg unop hr⟩, fun ⟨r, hr⟩ ↦ ⟨op r, congr_arg op hr⟩⟩

end

section

variable {F α β : Type*}

variable [MulOneClass α] [MulOneClass β] [FunLike F α β] [MonoidHomClass F α β]

theorem isSquare_subset_image_isSquare {f : F} (hf : Function.Surjective f) :
    {b | IsSquare b} ⊆ f '' {a | IsSquare a} := fun b ⟨s, _⟩ => by
  rcases hf s with ⟨r, rfl⟩
  exact ⟨r * r, by simp [*]⟩

end
