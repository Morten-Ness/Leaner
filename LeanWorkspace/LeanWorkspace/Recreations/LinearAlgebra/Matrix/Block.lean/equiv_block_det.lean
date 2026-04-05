import Mathlib

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]

theorem equiv_block_det (M : Matrix m m R) {p q : m → Prop} [DecidablePred p] [DecidablePred q]
    (e : ∀ x, q x ↔ p x) : (toSquareBlockProp M p).det = (toSquareBlockProp M q).det := by
  convert Matrix.det_reindex_self (Equiv.subtypeEquivRight e) (toSquareBlockProp M q)

-- Removed `@[simp]` attribute,
-- as the LHS simplifies already to `M.toSquareBlock id i ⟨i, ⋯⟩ ⟨i, ⋯⟩`

