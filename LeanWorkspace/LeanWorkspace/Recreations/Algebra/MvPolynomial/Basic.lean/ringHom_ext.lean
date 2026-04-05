import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem ringHom_ext {A : Type*} [Semiring A] {f g : MvPolynomial σ R →+* A}
    (hC : ∀ r, f (MvPolynomial.C r) = g (MvPolynomial.C r)) (hX : ∀ i, f (MvPolynomial.X i) = g (MvPolynomial.X i)) : f = g := by
  refine AddMonoidAlgebra.ringHom_ext' ?_ ?_
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): this has high priority, but Lean still chooses `RingHom.ext`, why?
  -- probably because of the type synonym
  · ext x
    exact hC _
  · apply Finsupp.mulHom_ext'; intro x
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `Finsupp.mulHom_ext'` needs to have increased priority
    apply MonoidHom.ext_mnat
    exact hX _

