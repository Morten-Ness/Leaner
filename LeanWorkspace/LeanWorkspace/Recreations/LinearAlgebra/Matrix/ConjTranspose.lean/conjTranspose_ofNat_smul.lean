import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem conjTranspose_ofNat_smul [Semiring R] [AddCommMonoid α] [StarAddMonoid α] [Module R α]
    (c : ℕ) [c.AtLeastTwo] (M : Matrix m n α) :
    ((ofNat(c) : R) • M)ᴴ = (OfNat.ofNat c : R) • Mᴴ := Matrix.conjTranspose_natCast_smul c M

