import Mathlib

variable {α β : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Ring β]
  {abv : β → α} [IsAbsoluteValue abv]
  {f g : ℕ → β} {a : ℕ → α}

variable [Archimedean α]

theorem geo_series_const (a : α) {x : α} (hx1 : |x| < 1) :
    IsCauSeq abs fun m ↦ ∑ n ∈ range m, (a * x ^ n) := by
  simpa [mul_sum, Pi.mul_def] using (const a).mul (IsCauSeq.geo_series x hx1)

