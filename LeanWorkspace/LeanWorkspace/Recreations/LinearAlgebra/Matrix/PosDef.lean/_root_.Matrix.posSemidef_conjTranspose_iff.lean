import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

theorem _root_.Matrix.posSemidef_conjTranspose_iff {M : Matrix n n R} :
    Mᴴ.PosSemidef ↔ M.PosSemidef := ⟨(by simpa using ·.conjTranspose), .conjTranspose⟩

protected lemma add [AddLeftMono R] {A : Matrix m m R} {B : Matrix m m R}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (A + B).PosSemidef :=
  ⟨Matrix.PosSemidef.isHermitian hA.add Matrix.PosSemidef.isHermitian hB, fun x => by
    simpa [mul_add, add_mul] using add_nonneg (hA.2 x) (hB.2 x)⟩

