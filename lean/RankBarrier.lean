/-
# A rank barrier for a support pattern

Source: OpenAI, "The Exponential Time Hypothesis is False" (17 Oct 2026, rev. 25 Oct), §4.1–4.3, the support
condition (2.14)/(4.4) on the interpolation matrix M₀. The statement and its proof in plain mathematics are in this
package's README.md.

Setting. `B r Q = (Fin Q → Fin r) × (Fin Q → Fin r)`, written `u = (a, d)`. `mism u w` is the number of coordinates
`s` with `w.1 s ≠ u.2 s` (where `a_w` differs from `d_u`). `kappa y` is the number of `s` with `r / 2 ≤ (y s).val`,
i.e. whose letter is among the top ⌈r/2⌉ of `Fin r`.

What is proved (`rank_barrier`). Over any field `F`, for all naturals `r, Q, R` and every `M : Matrix (B r Q) (B r Q) F`
with `M u w ≠ 0 → mism u w < R` (i.e. ≤ R − 1):

  #{u | kappa u.1 + R ≤ kappa u.2} ≤ rank (1 − M).

No norm condition, no restriction to the swap span, no hypothesis on r, Q, R. `rank_barrier_of_lipschitz` is the same
for any `κ` that is 1-Lipschitz for Hamming distance; `card_le_rank_of_triangular` is the general step (a finite set on
which `N` has unit diagonal and whose off-diagonal nonzeros strictly increase a key has size ≤ rank N).
`card_S_2_3_2` checks the tiny case: for (r, Q, R) = (2, 3, 2) the set has 7 elements.

What it does not say. Nothing about the probability form `D·Pr[Z₁ + … + Z_Q ≥ R]` or its e^{−Θ(R²/Q)} asymptotics;
nothing about OpenAI's paper's own M₀ beyond its support (that M₀ satisfies (2.14)/(4.4) is taken from the paper);
nothing about a different index set, measurement matrices that vary with the evaluation point, Appendix D's tensor
route, or Anthropic's recursion. It is a lower bound only and is not tight: at (2, 3, 2) the optimum is 8, not 7
(`scripts/mais.py`, not checked here). Control: `controls/must-pass.lean` shows that with `mism u w ≤ R` the
conclusion fails at (r, Q, R) = (2, 1, 1).
-/
import Mathlib

namespace RankBarrier

open Matrix Finset

/-- A finite set `S` on which `N` has unit diagonal, and whose off-diagonal nonzero entries go from a smaller to a
strictly larger value of `k`, has at most `rank N` elements: `N[S,S]` is unit upper triangular once `S` is ordered
by `k`. -/
theorem card_le_rank_of_triangular {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (N : Matrix ι ι F) (S : Finset ι) (k : ι → ℕ)
    (hdiag : ∀ u ∈ S, N u u = 1)
    (hoff : ∀ u ∈ S, ∀ w ∈ S, u ≠ w → N u w ≠ 0 → k u < k w) :
    S.card ≤ N.rank := by
  set A : Matrix S S F := N.submatrix Subtype.val Subtype.val with hA
  have hU : IsUnit A := by
    let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
    let b : S → ℕ ×ₗ Fin (Fintype.card S) := fun u => toLex (k u, e u)
    have hb : Function.Injective b := fun x y h => e.injective (congrArg (fun p => (ofLex p).2) h)
    let _ : LinearOrder S := LinearOrder.lift' b hb
    have hT : A.IsUpperTriangular := by
      intro i j hji
      change b j < b i at hji
      by_contra h
      have hij : (i : ι) ≠ j := fun hij => (lt_irrefl _ (Subtype.ext hij ▸ hji))
      have hk := hoff i i.2 j j.2 hij h
      rcases Prod.Lex.toLex_lt_toLex.mp hji with h1 | ⟨h1, _⟩
      · exact absurd hk (by simp at h1; omega)
      · exact absurd hk (by simp at h1; omega)
    rw [Matrix.isUnit_iff_isUnit_det, det_of_isUpperTriangular hT]
    simp [A, hdiag]
  calc S.card = Fintype.card S := (Fintype.card_coe S).symm
    _ = A.rank := (rank_of_isUnit A hU).symm
    _ ≤ N.rank := rank_submatrix_le N _ _

/-- Hamming distance between two words. -/
def ham {r Q : ℕ} (y y' : Fin Q → Fin r) : ℕ := (univ.filter fun s => y s ≠ y' s).card

/-- The index set of OpenAI §4.1: pairs `u = (a, d)` of words of length `Q` over `Fin r`. -/
abbrev B (r Q : ℕ) := (Fin Q → Fin r) × (Fin Q → Fin r)

/-- `mism u w = #{s | a_w(s) ≠ d_u(s)}`, the quantity bounded in the support condition (2.14)/(4.4). -/
def mism {r Q : ℕ} (u w : B r Q) : ℕ := (univ.filter fun s => w.1 s ≠ u.2 s).card

/-- The number of coordinates whose letter is among the top ⌈r/2⌉ of `Fin r`. -/
def kappa {r Q : ℕ} (y : Fin Q → Fin r) : ℕ := (univ.filter fun s => r / 2 ≤ (y s).val).card

/-- Any count of coordinates satisfying a fixed predicate is 1-Lipschitz for Hamming distance. -/
theorem count_lipschitz {r Q : ℕ} (P : Fin r → Prop) [DecidablePred P] (y y' : Fin Q → Fin r) :
    (univ.filter fun s => P (y s)).card ≤ (univ.filter fun s => P (y' s)).card + ham y y' := by
  calc (univ.filter fun s => P (y s)).card
      ≤ ((univ.filter fun s => P (y' s)) ∪ (univ.filter fun s => y s ≠ y' s)).card := by
        apply card_le_card
        intro s hs
        simp only [mem_filter, mem_univ, true_and, mem_union] at hs ⊢
        by_cases h : y s = y' s
        · exact Or.inl (h ▸ hs)
        · exact Or.inr h
    _ ≤ _ := card_union_le _ _

theorem kappa_lipschitz {r Q : ℕ} (y y' : Fin Q → Fin r) : kappa y ≤ kappa y' + ham y y' :=
  count_lipschitz (fun c : Fin r => r / 2 ≤ c.val) y y'

/-- (B) for any key `κ` that is 1-Lipschitz for Hamming distance. -/
theorem rank_barrier_of_lipschitz {F : Type*} [Field F] {r Q : ℕ} (R : ℕ)
    (κ : (Fin Q → Fin r) → ℕ) (hκ : ∀ y y', κ y ≤ κ y' + ham y y')
    (M : Matrix (B r Q) (B r Q) F) (hM : ∀ u w, M u w ≠ 0 → mism u w < R) :
    (univ.filter fun u : B r Q => κ u.1 + R ≤ κ u.2).card ≤ (1 - M).rank := by
  -- `κ d_u ≤ κ a_w + mism u w`
  have key : ∀ u w : B r Q, κ u.2 ≤ κ w.1 + mism u w := by
    intro u w
    have h := hκ u.2 w.1
    have : ham u.2 w.1 = mism u w := by
      unfold ham mism; congr 1; ext s; simp [ne_comm]
    omega
  apply card_le_rank_of_triangular (1 - M) _ (fun u => κ u.1)
  · intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu
    have h0 : M u u = 0 := by
      by_contra h
      have := hM u u h; have := key u u; omega
    simp [h0]
  · intro u hu w _ huw hN
    simp only [mem_filter, mem_univ, true_and] at hu
    have h : M u w ≠ 0 := by simpa [one_apply_ne huw] using hN
    have := hM u w h; have := key u w; omega

/-- **(B).** Every matrix with the support pattern (2.14)/(4.4) has
`rank (1 − M) ≥ #{u | κ(d_u) − κ(a_u) ≥ R}`. -/
theorem rank_barrier {F : Type*} [Field F] {r Q : ℕ} (R : ℕ)
    (M : Matrix (B r Q) (B r Q) F) (hM : ∀ u w, M u w ≠ 0 → mism u w < R) :
    (univ.filter fun u : B r Q => kappa u.1 + R ≤ kappa u.2).card ≤ (1 - M).rank :=
  rank_barrier_of_lipschitz R kappa kappa_lipschitz M hM

/-- The tiny case (r, Q, R) = (2, 3, 2), D = 64: the set has 7 elements. -/
theorem card_S_2_3_2 :
    (univ.filter fun u : B 2 3 => kappa u.1 + 2 ≤ kappa u.2).card = 7 := by
  decide

end RankBarrier
