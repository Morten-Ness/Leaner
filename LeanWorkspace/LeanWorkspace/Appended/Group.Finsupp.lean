import Mathlib

section

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

theorem addCommute_of_disjoint {f g : ι →₀ M} (h : Disjoint f.support g.support) :
    AddCommute f g := by
  classical simp_all [Finsupp.addCommute_iff_inter, Finset.disjoint_iff_inter_eq_empty]

end

section

variable {ι F M N O G H : Type*}

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid O]

theorem mapRange.addEquiv_symm (e : M ≃+ N) :
    (Finsupp.mapRange.addEquiv (ι := ι) e).symm = Finsupp.mapRange.addEquiv e.symm := rfl

end

section

variable {ι F M N O G H : Type*}

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid O]

theorem mapRange.addEquiv_toAddMonoidHom (e : M ≃+ N) :
    Finsupp.mapRange.addEquiv (ι := ι) e = Finsupp.mapRange.addMonoidHom (ι := ι) e.toAddMonoidHom := rfl

end

section

variable {ι F M N O G H : Type*}

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid O]

theorem mapRange.addEquiv_trans (e₁ : M ≃+ N) (e₂ : N ≃+ O) :
    Finsupp.mapRange.addEquiv (ι := ι) (e₁.trans e₂) =
      (Finsupp.mapRange.addEquiv e₁).trans (Finsupp.mapRange.addEquiv e₂) := by ext; simp

end

section

variable {ι F M N O G H : Type*}

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid O]

theorem mapRange.addMonoidHom_comp (f : N →+ O) (g : M →+ N) :
    Finsupp.mapRange.addMonoidHom (ι := ι) (f.comp g) =
      (Finsupp.mapRange.addMonoidHom f).comp (Finsupp.mapRange.addMonoidHom g) := by ext; simp

end

section

variable {ι F M N O G H : Type*}

variable [Zero M] [Zero N] [Zero O]

theorem mapRange.zeroHom_comp (f : ZeroHom N O) (f₂ : ZeroHom M N) :
    Finsupp.mapRange.zeroHom (ι := ι) (f.comp f₂) = (Finsupp.mapRange.zeroHom f).comp (Finsupp.mapRange.zeroHom f₂) := by
  ext; simp

end
