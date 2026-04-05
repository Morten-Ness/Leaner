import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable (hli : LinearIndependent R v) (hsp : ⊤ ≤ span R (range v))

theorem mk_coord_apply [DecidableEq ι] {i j : ι} :
    (Module.Basis.mk hli hsp).coord i (v j) = if j = i then 1 else 0 := by
  rcases eq_or_ne j i with h | h
  · simp only [h, if_true, Module.Basis.mk_coord_apply_eq i]
  · simp only [h, if_false, Module.Basis.mk_coord_apply_ne h]

