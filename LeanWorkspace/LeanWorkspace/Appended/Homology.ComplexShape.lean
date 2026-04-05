import Mathlib

section

variable {ι : Type*}

theorem next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Rel i j) : c.next i = j := by
  apply c.next_eq _ h
  rw [ComplexShape.next]
  rw [dif_pos]
  exact Exists.choose_spec ⟨j, h⟩

end

section

variable {ι : Type*}

theorem next_eq_self (c : ComplexShape ι) (j : ι) (hj : ¬c.Rel j (c.next j)) :
    c.next j = j := ComplexShape.next_eq_self' c j (fun k hk' => hj (by simpa only [ComplexShape.next_eq' c hk'] using hk'))

end

section

variable {ι : Type*}

theorem symm_bijective :
    Function.Bijective (ComplexShape.symm : ComplexShape ι → ComplexShape ι) := Function.bijective_iff_has_inverse.mpr ⟨_, ComplexShape.symm_symm, ComplexShape.symm_symm⟩

end
