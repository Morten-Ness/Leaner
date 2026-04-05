import Mathlib

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

theorem fwdDiff_smul {R : Type*} [Ring R] [Module R G] (f : M → R) (g : M → G) :
    Δ_[h] (f • g) = Δ_[h] f • g + f • Δ_[h] g + Δ_[h] f • Δ_[h] g := by
  ext y
  simp only [fwdDiff, Pi.smul_apply', Pi.add_apply, smul_sub, sub_smul]
  abel

-- Note `fwdDiff_const_smul` is more general than `fwdDiff_smul` since it allows `R` to be a
-- semiring, rather than a ring; in particular `R = ℕ` is allowed.

