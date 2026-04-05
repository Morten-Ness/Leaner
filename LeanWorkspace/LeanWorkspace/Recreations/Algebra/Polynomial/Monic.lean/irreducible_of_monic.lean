import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [CommSemiring R] {p : R[X]}

variable [NoZeroDivisors R] {p q : R[X]}

theorem irreducible_of_monic (hp : p.Monic) (hp1 : p ≠ 1) :
    Irreducible p ↔ ∀ f g : R[X], f.Monic → g.Monic → f * g = p → f = 1 ∨ g = 1 := by
  refine
    ⟨fun h f g hf hg hp => (h.2 hp.symm).imp hf.eq_one_of_isUnit hg.eq_one_of_isUnit, fun h =>
      ⟨hp1 ∘ hp.eq_one_of_isUnit, fun f g hfg =>
        (h (g * Polynomial.C f.leadingCoeff) (f * Polynomial.C g.leadingCoeff) ?_ ?_ ?_).symm.imp
          (.of_mul_eq_one _)
          (.of_mul_eq_one _)⟩⟩
  · rwa [Polynomial.Monic, leadingCoeff_mul, leadingCoeff_C, ← leadingCoeff_mul, mul_comm, ← hfg, ← Polynomial.Monic]
  · rwa [Polynomial.Monic, leadingCoeff_mul, leadingCoeff_C, ← leadingCoeff_mul, ← hfg, ← Polynomial.Monic]
  · rw [mul_mul_mul_comm, ← C_mul, ← leadingCoeff_mul, ← hfg, hp.leadingCoeff, C_1, mul_one,
      mul_comm, ← hfg]

