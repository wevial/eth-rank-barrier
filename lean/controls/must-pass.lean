import RankBarrier
open RankBarrier Finset
-- P1: weaken the support condition to `mism u w ≤ R` and the conclusion fails. (r, Q, R) = (2, 1, 1): every `mism`
-- is ≤ Q = 1, so M = 1 is allowed; rank (1 − 1) = 0, but u = (a, d) = (0, 1) is in the set (κ a = 0, κ d = 1).
theorem weakened_fails :
    ¬ ∀ M : Matrix (B 2 1) (B 2 1) ℚ, (∀ u w, M u w ≠ 0 → mism u w ≤ 1) →
      (univ.filter fun u : B 2 1 => kappa u.1 + 1 ≤ kappa u.2).card ≤ (1 - M).rank := by
  intro h
  have h1 := h 1 (fun u w _ => (card_le_univ _).trans (by simp))
  rw [sub_self, Matrix.rank_zero] at h1
  have hc : (univ.filter fun u : B 2 1 => kappa u.1 + 1 ≤ kappa u.2).card = 1 := by decide
  omega
-- P2: the tiny case (r, Q, R) = (2, 3, 2): the set has 7 elements (README.md's table, row "the set S").
example : (univ.filter fun u : B 2 3 => kappa u.1 + 2 ≤ kappa u.2).card = 7 := card_S_2_3_2
#print axioms rank_barrier
#print axioms rank_barrier_of_lipschitz
#print axioms card_le_rank_of_triangular
#print axioms card_S_2_3_2
#print axioms weakened_fails
