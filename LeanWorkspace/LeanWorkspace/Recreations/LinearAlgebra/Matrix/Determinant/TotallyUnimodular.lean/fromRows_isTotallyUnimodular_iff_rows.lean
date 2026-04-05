import Mathlib

variable {m m' n n' R : Type*} [CommRing R]

theorem fromRows_isTotallyUnimodular_iff_rows [DecidableEq n] {A : Matrix m n R} {B : Matrix m' n R}
    (hB : Nonempty n → ∀ i : m', ∃ j : n, ∃ s : SignType, B i = Pi.single j s.cast) :
    (fromRows A B).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := ⟨.submatrix Sum.inl id, fun hA => hA.fromRows_unitlike hB⟩

