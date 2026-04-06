FAIL
import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable {κ : Type*}

theorem lequivCongrLeft_symm_lof [DecidableEq ι] [DecidableEq κ] {h : ι ≃ κ}
    {k : κ} {x : M (h.symm k)} :
    (DirectSum.lequivCongrLeft R h).symm (DirectSum.lof R κ (fun k => M (h.symm k)) k x) = DirectSum.lof R ι M (h.symm k) x := by
  ext i y
  simp [DirectSum.lequivCongrLeft]
