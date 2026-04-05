import Mathlib

variable {α : Type*} {g : GenContFract α} {n : ℕ}

theorem exists_s_b_of_partDen {b : α}
    (nth_partDen_eq : g.partDens.get? n = some b) :
    ∃ gp, g.s.get? n = some gp ∧ gp.b = b := by
  simpa [partDens, Stream'.Seq.map_get?] using nth_partDen_eq

