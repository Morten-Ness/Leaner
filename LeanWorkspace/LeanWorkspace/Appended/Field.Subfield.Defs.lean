import Mathlib

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (S : Type*) [SetLike S K] [h : SubfieldClass S K]

variable {S} {x : K}

theorem nnqsmul_mem (s : S) (q : ℚ≥0) (hx : x ∈ s) : q • x ∈ s := by
  simpa only [NNRat.smul_def] using mul_mem (SubfieldClass.nnratCast_mem _ _) hx

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (S : Type*) [SetLike S K] [h : SubfieldClass S K]

variable {S} {x : K}

theorem nnratCast_mem (s : S) (q : ℚ≥0) : (q : K) ∈ s := by
  simpa only [NNRat.cast_def] using div_mem (natCast_mem s q.num) (natCast_mem s q.den)

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (S : Type*) [SetLike S K] [h : SubfieldClass S K]

variable {S} {x : K}

theorem ofScientific_mem (s : S) {b : Bool} {n m : ℕ} :
    (OfScientific.ofScientific n b m : K) ∈ s := SubfieldClass.nnratCast_mem s (OfScientific.ofScientific n b m)

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (S : Type*) [SetLike S K] [h : SubfieldClass S K]

variable {S} {x : K}

theorem qsmul_mem (s : S) (q : ℚ) (hx : x ∈ s) : q • x ∈ s := by
  simpa only [Rat.smul_def] using mul_mem (SubfieldClass.ratCast_mem _ _) hx

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (S : Type*) [SetLike S K] [h : SubfieldClass S K]

variable {S} {x : K}

theorem ratCast_mem (s : S) (q : ℚ) : (q : K) ∈ s := by
  simpa only [Rat.cast_def] using div_mem (intCast_mem s q.num) (natCast_mem s q.den)

end
