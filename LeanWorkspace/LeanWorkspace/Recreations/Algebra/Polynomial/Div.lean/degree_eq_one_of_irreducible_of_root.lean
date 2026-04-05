import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

variable [IsDomain R]

theorem degree_eq_one_of_irreducible_of_root (hi : Irreducible p) {x : R} (hx : IsRoot p x) :
    degree p = 1 := let ⟨g, hg⟩ := Polynomial.dvd_iff_isRoot.2 hx
  have : IsUnit (Polynomial.X - Polynomial.C x) ∨ IsUnit g := hi.isUnit_or_isUnit hg
  this.elim
    (fun h => by
      have h₁ : degree (Polynomial.X - Polynomial.C x) = 1 := degree_X_sub_C x
      have h₂ : degree (Polynomial.X - Polynomial.C x) = 0 := degree_eq_zero_of_isUnit h
      rw [h₁] at h₂; exact absurd h₂ (by decide))
    fun hgu => by rw [hg, degree_mul, degree_X_sub_C, degree_eq_zero_of_isUnit hgu, add_zero]

