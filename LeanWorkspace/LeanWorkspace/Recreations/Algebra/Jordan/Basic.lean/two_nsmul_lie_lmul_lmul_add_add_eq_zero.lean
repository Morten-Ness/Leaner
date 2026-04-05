import Mathlib

variable (A : Type*)

variable {A} [NonUnitalNonAssocCommRing A]

variable [IsCommJordan A]

private theorem aux0 {a b c : A} : ⁅L (a + b + c), L ((a + b + c) * (a + b + c))⁆ =
    ⁅L a + L b + L c, L (a * a) + L (b * b) + L (c * c) +
    2 • L (a * b) + 2 • L (c * a) + 2 • L (b * c)⁆ := by
  rw [add_mul, add_mul]
  iterate 6 rw [mul_add]
  iterate 10 rw [map_add]
  rw [mul_comm b a, mul_comm c a, mul_comm c b]
  iterate 3 rw [two_smul]
  simp only [add_lie]
  abel_nf


private theorem aux1 {a b c : A} :
    ⁅L a + L b + L c, L (a * a) + L (b * b) + L (c * c) +
    2 • L (a * b) + 2 • L (c * a) + 2 • L (b * c)⁆
    =
    ⁅L a, L (a * a)⁆ + ⁅L a, L (b * b)⁆ + ⁅L a, L (c * c)⁆ +
    ⁅L a, 2 • L (a * b)⁆ + ⁅L a, 2 • L (c * a)⁆ + ⁅L a, 2 • L (b * c)⁆ +
    (⁅L b, L (a * a)⁆ + ⁅L b, L (b * b)⁆ + ⁅L b, L (c * c)⁆ +
    ⁅L b, 2 • L (a * b)⁆ + ⁅L b, 2 • L (c * a)⁆ + ⁅L b, 2 • L (b * c)⁆) +
    (⁅L c, L (a * a)⁆ + ⁅L c, L (b * b)⁆ + ⁅L c, L (c * c)⁆ +
    ⁅L c, 2 • L (a * b)⁆ + ⁅L c, 2 • L (c * a)⁆ + ⁅L c, 2 • L (b * c)⁆) := by
  rw [add_lie, add_lie]
  iterate 15 rw [lie_add]


private theorem aux2 {a b c : A} :
    ⁅L a, L (a * a)⁆ + ⁅L a, L (b * b)⁆ + ⁅L a, L (c * c)⁆ +
    ⁅L a, 2 • L (a * b)⁆ + ⁅L a, 2 • L (c * a)⁆ + ⁅L a, 2 • L (b * c)⁆ +
    (⁅L b, L (a * a)⁆ + ⁅L b, L (b * b)⁆ + ⁅L b, L (c * c)⁆ +
    ⁅L b, 2 • L (a * b)⁆ + ⁅L b, 2 • L (c * a)⁆ + ⁅L b, 2 • L (b * c)⁆) +
    (⁅L c, L (a * a)⁆ + ⁅L c, L (b * b)⁆ + ⁅L c, L (c * c)⁆ +
    ⁅L c, 2 • L (a * b)⁆ + ⁅L c, 2 • L (c * a)⁆ + ⁅L c, 2 • L (b * c)⁆)
    =
    ⁅L a, L (b * b)⁆ + ⁅L b, L (a * a)⁆ + 2 • (⁅L a, L (a * b)⁆ + ⁅L b, L (a * b)⁆) +
    (⁅L a, L (c * c)⁆ + ⁅L c, L (a * a)⁆ + 2 • (⁅L a, L (c * a)⁆ + ⁅L c, L (c * a)⁆)) +
    (⁅L b, L (c * c)⁆ + ⁅L c, L (b * b)⁆ + 2 • (⁅L b, L (b * c)⁆ + ⁅L c, L (b * c)⁆)) +
    (2 • ⁅L a, L (b * c)⁆ + 2 • ⁅L b, L (c * a)⁆ + 2 • ⁅L c, L (a * b)⁆) := by
  rw [(commute_lmul_lmul_sq a).lie_eq, (commute_lmul_lmul_sq b).lie_eq,
    (commute_lmul_lmul_sq c).lie_eq, zero_add, add_zero, add_zero]
  simp only [lie_nsmul]
  abel


private theorem aux3 {a b c : A} :
    ⁅L a, L (b * b)⁆ + ⁅L b, L (a * a)⁆ + 2 • (⁅L a, L (a * b)⁆ + ⁅L b, L (a * b)⁆) +
    (⁅L a, L (c * c)⁆ + ⁅L c, L (a * a)⁆ + 2 • (⁅L a, L (c * a)⁆ + ⁅L c, L (c * a)⁆)) +
    (⁅L b, L (c * c)⁆ + ⁅L c, L (b * b)⁆ + 2 • (⁅L b, L (b * c)⁆ + ⁅L c, L (b * c)⁆)) +
    (2 • ⁅L a, L (b * c)⁆ + 2 • ⁅L b, L (c * a)⁆ + 2 • ⁅L c, L (a * b)⁆)
    =
    2 • ⁅L a, L (b * c)⁆ + 2 • ⁅L b, L (c * a)⁆ + 2 • ⁅L c, L (a * b)⁆ := by
  rw [add_eq_right]
  nth_rw 2 [mul_comm a b]
  nth_rw 1 [mul_comm c a]
  nth_rw 2 [mul_comm b c]
  iterate 3 rw [two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add]
  iterate 2 rw [← lie_skew (L (a * a)), ← lie_skew (L (b * b)), ← lie_skew (L (c * c))]
  abel


theorem two_nsmul_lie_lmul_lmul_add_add_eq_zero (a b c : A) :
    2 • (⁅L a, L (b * c)⁆ + ⁅L b, L (c * a)⁆ + ⁅L c, L (a * b)⁆) = 0 := by
  symm
  calc
    0 = ⁅L (a + b + c), L ((a + b + c) * (a + b + c))⁆ := by
      rw [(commute_lmul_lmul_sq (a + b + c)).lie_eq]
    _ = _ := by rw [aux0, aux1, aux2, aux3, nsmul_add, nsmul_add]

