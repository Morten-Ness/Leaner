import Mathlib

variable {F α β R S S' : Type*}

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] (f : R ≃+* S) (x : R)

variable [FunLike F R S]

theorem piCongrLeft'_symm {R : Type*} [NonUnitalNonAssocSemiring R] (e : α ≃ β) :
    (RingEquiv.piCongrLeft' (fun _ => R) e).symm = RingEquiv.piCongrLeft' _ e.symm := by
  simp only [RingEquiv.piCongrLeft', RingEquiv.symm, MulEquiv.symm, Equiv.piCongrLeft'_symm]

