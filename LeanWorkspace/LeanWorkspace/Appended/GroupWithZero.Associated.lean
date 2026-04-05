import Mathlib

section

variable {M : Type*}

variable [CommMonoid M]

theorem coe_unit_eq_one (u : (Associates M)ˣ) : (u : Associates M) = 1 := by
  simp [eq_iff_true_of_subsingleton]

end

section

variable {M : Type*}

theorem forall_associated [Monoid M] {p : Associates M → Prop} :
    (∀ a, p a) ↔ ∀ a, p (Associates.mk a) := Iff.intro (fun h _ => h _) fun h a => Quotient.inductionOn a h

end

section

variable {M : Type*}

variable [CommMonoidWithZero M]

theorem irreducible_iff_prime_iff :
    (∀ a : M, Irreducible a ↔ Prime a) ↔ ∀ a : Associates M, Irreducible a ↔ Prime a := by
  simp_rw [Associates.forall_associated, Associates.irreducible_mk, Associates.prime_mk]

end

section

variable {M : Type*}

variable [CommMonoid M]

theorem isUnit_iff_eq_bot {a : Associates M} : IsUnit a ↔ a = ⊥ := by
  rw [Associates.isUnit_iff_eq_one, Associates.bot_eq_one]

end

section

variable {M : Type*}

variable [CommMonoidWithZero M] [IsCancelMulZero M]

theorem le_one_iff {p : Associates M} : p ≤ 1 ↔ p = 1 := by rw [← Associates.bot_eq_one, le_bot_iff]

end

section

variable {M : Type*}

theorem map {M N : Type*} [Monoid M] [Monoid N] {F : Type*} [FunLike F M N] [MonoidHomClass F M N]
    (f : F) {x y : M} (ha : Associated x y) : Associated (f x) (f y) := by
  obtain ⟨u, ha⟩ := ha
  exact ⟨Units.map f u, by rw [← ha, map_mul, Units.coe_map, MonoidHom.coe_coe]⟩

end

section

variable {M : Type*}

theorem mk_eq_one [Monoid M] {a : M} : Associates.mk a = 1 ↔ IsUnit a := by
  rw [← Associates.mk_one, Associates.mk_eq_mk_iff_associated, associated_one_iff_isUnit]

end

section

variable {M : Type*}

theorem mk_injective [Monoid M] [Subsingleton Mˣ] : Function.Injective (@Associates.mk M _) := fun _ _ h => associated_iff_eq.mp (Associates.mk_eq_mk_iff_associated.mp h)

end

section

variable {M : Type*}

variable [CommMonoid M]

theorem mk_isRelPrime_iff {a b : M} :
    IsRelPrime (Associates.mk a) (Associates.mk b) ↔ IsRelPrime a b := by
  simp_rw [IsRelPrime, Associates.forall_associated, Associates.mk_dvd_mk, Associates.isUnit_mk]

end

section

variable {M : Type*}

variable [CommMonoid M]

theorem mul_mono {a b c d : Associates M} (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d := let ⟨x, hx⟩ := h₁
  let ⟨y, hy⟩ := h₂
  ⟨x * y, by simp [hx, hy, mul_comm, mul_left_comm]⟩

end

section

variable {M : Type*}

variable [CommMonoidWithZero M]

theorem prime_mk {p : M} : Prime (Associates.mk p) ↔ Prime p := by
  rw [Prime, _root_.Prime, Associates.forall_associated]
  simp only [Associates.forall_associated, Associates.mk_ne_zero, Associates.isUnit_mk, Associates.mk_mul_mk, Associates.mk_dvd_mk]

end

section

variable {M : Type*}

theorem quot_out [Monoid M] (a : Associates M) : Associates.mk (Quot.out a) = a := by
  rw [← Associates.quot_mk_eq_mk, Quot.out_eq]

end

section

variable {M : Type*}

variable [MonoidWithZero M]

theorem quot_out_zero : Quot.out (0 : Associates M) = 0 := by rw [← Associates.mk_eq_zero, Associates.quot_out]

end
