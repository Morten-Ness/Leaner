import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

theorem Affine.Simplex.span_eq_top [FiniteDimensional k V] {n : ℕ} (T : Affine.Simplex k V n)
    (hrank : finrank k V = n) : affineSpan k (Set.range T.points) = ⊤ := by
  rw [AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one T.independent,
    Fintype.card_fin, hrank]

