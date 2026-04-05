import Mathlib

section

variable {M : Type*} {N : Type*}

variable {A M₁ : Type*} [SetLike A M₁] [One M₁] [hA : OneMemClass A M₁] (S' : A)

theorem coe_eq_one {x : S'} : (↑x : M₁) = 1 ↔ x = 1 := (Subtype.ext_iff.symm : (x : M₁) = (1 : S') ↔ x = 1)

end

section

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

variable [MulOneClass N]

theorem eqLocusM_same (f : M →* N) : f.eqLocusM f = ⊤ := SetLike.ext fun _ => eq_self_iff_true _

end

section

variable {M : Type*} {N : Type*}

variable {A : Type*} [MulOneClass M] [SetLike A M] [hA : SubmonoidClass A M] (S' : A)

theorem mk_pow {M} [Monoid M] {A : Type*} [SetLike A M] [SubmonoidClass A M] {S : A} (x : M)
    (hx : x ∈ S) (n : ℕ) : (⟨x, hx⟩ : S) ^ n = ⟨x ^ n, pow_mem hx n⟩ := rfl

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.

end

section

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

theorem toSubsemigroup_inj {s t : Submonoid M} : s.toSubsemigroup = t.toSubsemigroup ↔ s = t := Submonoid.toSubsemigroup_injective.eq_iff

end
