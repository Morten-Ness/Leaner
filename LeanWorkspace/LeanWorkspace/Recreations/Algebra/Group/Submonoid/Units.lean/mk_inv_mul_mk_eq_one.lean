import Mathlib

variable {M : Type*} [Monoid M]

theorem mk_inv_mul_mk_eq_one (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) :
    (⟨_, h.2⟩ : S) * ⟨_, h.1⟩ = 1 := Subtype.ext x.inv_mul

