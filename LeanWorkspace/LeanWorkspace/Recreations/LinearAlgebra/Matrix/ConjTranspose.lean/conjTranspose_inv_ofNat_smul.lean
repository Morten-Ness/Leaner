import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem conjTranspose_inv_ofNat_smul [DivisionSemiring R] [AddCommMonoid α] [StarAddMonoid α]
    [Module R α] (c : ℕ) [c.AtLeastTwo] (M : Matrix m n α) :
    ((ofNat(c) : R)⁻¹ • M)ᴴ = (OfNat.ofNat c : R)⁻¹ • Mᴴ := Matrix.conjTranspose_inv_natCast_smul c M

