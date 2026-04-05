import Mathlib

section

variable {X G : Type*} {A B C : Set X}

variable [SMul G X]

theorem restr_of_source_subset {f : Equidecomp X G} {A : Set X} (hA : f.source ⊆ A) :
    f.restr A = f := by
  apply Equidecomp.toPartialEquiv_injective
  rw [Equidecomp.toPartialEquiv_restr, PartialEquiv.restr_eq_of_source_subset hA]

end

section

variable {X G : Type*} {A B C : Set X}

variable [Group G] [MulAction G X]

theorem symm_bijective : Function.Bijective (Equidecomp.symm : Equidecomp X G → _) := Equidecomp.symm_involutive.bijective

end
