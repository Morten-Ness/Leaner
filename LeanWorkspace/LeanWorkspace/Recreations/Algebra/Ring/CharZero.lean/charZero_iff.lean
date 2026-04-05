import Mathlib

variable {α R S : Type*} {n : ℕ}

variable [NonAssocSemiring R] [NonAssocSemiring S]

theorem charZero_iff {ϕ : R →+* S} (hϕ : Function.Injective ϕ) : CharZero R ↔ CharZero S := ⟨fun hR =>
    ⟨by intro a b h; rwa [← @Nat.cast_inj R, ← hϕ.eq_iff, map_natCast ϕ, map_natCast ϕ]⟩,
    fun _ => ϕ.charZero⟩

