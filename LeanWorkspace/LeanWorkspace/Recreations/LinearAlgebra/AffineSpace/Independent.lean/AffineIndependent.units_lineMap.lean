import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

theorem AffineIndependent.units_lineMap {p : ι → P} (hp : AffineIndependent k p) (j : ι)
    (w : ι → Units k) : AffineIndependent k fun i => AffineMap.lineMap (p j) (p i) (w i : k) := by
  rw [affineIndependent_iff_linearIndependent_vsub k _ j] at hp ⊢
  simp only [AffineMap.lineMap_vsub_left, AffineMap.coe_const, AffineMap.lineMap_same, const_apply]
  exact hp.units_smul fun i => w i

