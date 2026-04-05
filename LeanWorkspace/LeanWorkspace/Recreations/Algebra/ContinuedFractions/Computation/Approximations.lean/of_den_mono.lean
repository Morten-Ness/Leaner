import Mathlib

variable {K : Type*} {v : K} {n : ℕ} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

theorem of_den_mono : (of v).dens n ≤ (of v).dens (n + 1) := by
  let g := of v
  rcases Decidable.em <| g.partDens.TerminatedAt n with terminated | not_terminated
  · have : g.partDens.get? n = none := by rwa [Stream'.Seq.TerminatedAt] at terminated
    have : g.TerminatedAt n :=
      terminatedAt_iff_partDen_none.2 (by rwa [Stream'.Seq.TerminatedAt] at terminated)
    have : g.dens (n + 1) = g.dens n :=
      dens_stable_of_terminated n.le_succ this
    rw [this]
  · obtain ⟨b, nth_partDen_eq⟩ : ∃ b, g.partDens.get? n = some b :=
      Option.ne_none_iff_exists'.mp not_terminated
    have : 1 ≤ b := GenContFract.of_one_le_get?_partDen nth_partDen_eq
    calc
      g.dens n ≤ b * g.dens n := by
        simpa using mul_le_mul_of_nonneg_right this GenContFract.zero_le_of_den
      _ ≤ g.dens (n + 1) := GenContFract.le_of_succ_get?_den nth_partDen_eq

