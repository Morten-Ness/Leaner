import Mathlib

variable {M : Type*} [Monoid M]

theorem mk_mul_mk_inv_eq_one (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) :
    (⟨_, h.1⟩ : S) * ⟨_, h.2⟩ = 1 := Subtype.ext x.mul_inv

