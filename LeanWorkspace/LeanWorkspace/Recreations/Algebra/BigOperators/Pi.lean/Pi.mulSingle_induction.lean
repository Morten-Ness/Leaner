import Mathlib

open scoped Finset

variable {ι κ M N R α : Type*}

variable [Finite ι] [DecidableEq ι] {M : ι → Type*}

theorem Pi.mulSingle_induction [∀ i, CommMonoid (M i)] (p : (Π i, M i) → Prop) (f : Π i, M i)
    (one : p 1) (mul : ∀ f g, p f → p g → p (f * g))
    (mulSingle : ∀ i m, p (Pi.mulSingle i m)) : p f := by
  cases nonempty_fintype ι
  rw [← Finset.univ_prod_mulSingle f]
  exact Finset.prod_induction _ _ mul one (by simp [mulSingle])

