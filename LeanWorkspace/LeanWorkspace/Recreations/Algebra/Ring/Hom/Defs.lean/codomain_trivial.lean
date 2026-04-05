import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} (f : α →+* β)

theorem codomain_trivial (f : α →+* β) [h : Subsingleton α] : Subsingleton β := (subsingleton_or_nontrivial β).resolve_right fun _ =>
    not_nontrivial_iff_subsingleton.mpr h RingHom.domain_nontrivial f

