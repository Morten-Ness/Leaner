import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem conjTranspose_ofNat [DecidableEq n] [NonAssocSemiring α] [StarRing α] (d : ℕ)
    [d.AtLeastTwo] : (ofNat(d) : Matrix n n α)ᴴ = OfNat.ofNat d := Matrix.conjTranspose_natCast _

