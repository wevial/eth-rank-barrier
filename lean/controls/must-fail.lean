import RankBarrier
open RankBarrier Finset
-- F1: the main theorem with the support condition weakened to `mism u w ≤ R` (false: must-pass P1 is a
-- counterexample). The proof that worked for `< R` must not go through.
theorem F1 {F : Type*} [Field F] {r Q : ℕ} (R : ℕ)
    (M : Matrix (B r Q) (B r Q) F) (hM : ∀ u w, M u w ≠ 0 → mism u w ≤ R) :
    (univ.filter fun u : B r Q => kappa u.1 + R ≤ kappa u.2).card ≤ (1 - M).rank :=
  rank_barrier_of_lipschitz R kappa kappa_lipschitz M hM
-- F2: the tiny case's count off by one (it is 7).
example : (univ.filter fun u : B 2 3 => kappa u.1 + 2 ≤ kappa u.2).card = 8 := by decide
