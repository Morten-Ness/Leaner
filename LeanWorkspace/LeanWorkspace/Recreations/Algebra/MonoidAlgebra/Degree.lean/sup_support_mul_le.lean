import Mathlib

variable {R R' A T B ι : Type*}

variable [SemilatticeSup B] [OrderBot B] [SemilatticeInf T] [OrderTop T]

variable [Semiring R]

variable [Add A] [Add B] [Add T] [AddLeftMono B] [AddRightMono B]
  [AddLeftMono T] [AddRightMono T]

theorem sup_support_mul_le {degb : A → B} (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b)
    (f g : R[A]) :
    (f * g).support.sup degb ≤ f.support.sup degb + g.support.sup degb := by
  classical
  grw [support_mul, Finset.sup_add_le]
  rintro _fd fds _gd gds
  grw [degbm, ← Finset.le_sup fds, ← Finset.le_sup gds]

