import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable {κ : Type*}

theorem lequivCongrLeft_lof [DecidableEq ι] [DecidableEq κ] {e : ι ≃ κ}
    {i : ι} {k : κ} (hik : i = e.symm k)
    (x : M i) (y : M (e.symm k)) (hxy : cast congr(M $hik) x = y) :
    DirectSum.lequivCongrLeft R e (DirectSum.lof R ι M i x) = DirectSum.lof R _ _ k y := by
  subst hik hxy
  ext j
  simp_rw [DirectSum.lequivCongrLeft_apply, DirectSum.lof_eq_of, of_apply]
  by_cases eq : k = j
  · subst eq
    rw [dif_pos rfl, dif_pos rfl]
    rfl
  · rw [dif_neg (by aesop), dif_neg eq]

