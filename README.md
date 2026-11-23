# A rank barrier for the support pattern of OpenAI's interpolation matrix

Claude (Anthropic), with Ko Vial

OpenAI's "The Exponential Time Hypothesis is False" (17 October 2026, revised 25 October; `github.com/openai/math`, file `preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf`) builds, in §4.1–4.3, a matrix M₀ whose support obeys a mismatch condition, (2.14)/(4.4). The algorithm needs at least rank(I − M₀) measurement rows.

**Claim.** Every matrix with that support pattern, over any field, has rank(I − M) at least the size of an explicit set S. For √Q ≪ R ≪ Q that size is D·e^{−Θ(R²/Q)}, the same order as the paper's upper bound. So on this index set, with this support pattern, no choice of matrix lowers the number of measurement rows by more than a constant in the exponent.

This repository holds a Lean 4 proof of the claim's exact form, a must-pass and a must-fail control, and two scripts that settle the smallest nontrivial case exactly. One command, `./reproduce.sh`, checks all of it.

**Who did what.**

- Claude, Anthropic's AI model, did the mathematics, the code and the writing.
- Ko Vial gave Claude a research repository for its own questions and the machines the work ran on, suggested consulting other models, which is how this result was found, decided what was released, and published it.

This package comes from that repository. How the result was found is described below.

## The statement

**Setting** (OpenAI §4.1–4.3). Let B = ([r] × [r])^Q, with elements u = (a_u, d_u), two words of length Q over [r]. Its size is D = r^{2Q}. The support condition (2.14)/(4.4) on a B × B matrix M is

> M[u, w] ≠ 0 only if #{s : a_w(s) ≠ d_u(s)} ≤ R − 1.

Let κ(y) be the number of coordinates of y whose letter is among the top ⌈r/2⌉ letters of [r].

**Theorem.** Over any field, for every M with that support pattern,

> rank(I − M) ≥ |S|, where S = {u ∈ B : κ(d_u) − κ(a_u) ≥ R}.

No norm condition, no restriction to the span of the swaps, and no hypothesis on r, Q, R.

**As Lean prints it** (`#check @RankBarrier.rank_barrier`):

```
@RankBarrier.rank_barrier : ∀ {F : Type u_1} [inst : Field F] {r Q : ℕ} (R : ℕ)
  (M : Matrix (RankBarrier.B r Q) (RankBarrier.B r Q) F),
  (∀ (u w : RankBarrier.B r Q), M u w ≠ 0 → RankBarrier.mism u w < R) →
    {u | RankBarrier.kappa u.1 + R ≤ RankBarrier.kappa u.2}.card ≤ (1 - M).rank
```

Here `B r Q = (Fin Q → Fin r) × (Fin Q → Fin r)`, `mism u w = #{s | w.1 s ≠ u.2 s}`, and `kappa y = #{s | r / 2 ≤ (y s).val}`. The letters with `r / 2 ≤ c` are the top ⌈r/2⌉ of `Fin r`.

**Probability form** (not in Lean). For r ≥ 2 and 1 ≤ R ≤ Q, |S| = D·Pr[Z₁ + … + Z_Q ≥ R], where the Z_s are independent on {−1, 0, 1} with Pr[Z = 1] = Pr[Z = −1] = q(1 − q) and q = ⌈r/2⌉/r. For √Q ≪ R ≪ Q this is D·e^{−Θ(R²/Q)}. The paper's own interval gives rank(I − M₀) ≤ D·Pr[Bin(Q, (r−1)/2r) ∉ I] ≤ 2e^{−R²/(8Q)}·D (§2.7, Lemma 4.8).

## The proof

1. Take u, w ∈ S with M[u, w] ≠ 0.
2. Then a_w differs from d_u in at most R − 1 places, and κ is 1-Lipschitz for Hamming distance, so κ(a_w) ≥ κ(d_u) − (R − 1).
3. Since u ∈ S, κ(d_u) − (R − 1) ≥ κ(a_u) + 1. So inside S every nonzero entry of M goes to a strictly larger κ(a); in particular M[u, u] = 0.
4. Ordered by κ(a), the minor (I − M)[S, S] is upper triangular with unit diagonal, so it is invertible.
5. rank(I − M) ≥ rank of that minor = |S|. ∎

The last two steps are the standard lower bound on the min-rank of a zero pattern by a triangular minor. In Lean they are `card_le_rank_of_triangular`.

## What is in Lean and what is not

In Lean (`lean/RankBarrier.lean`, against Mathlib):

- `rank_barrier`: the theorem above.
- `rank_barrier_of_lipschitz`: the same for any key κ that is 1-Lipschitz for Hamming distance.
- `card_le_rank_of_triangular`: a finite set on which N has unit diagonal, and whose off-diagonal nonzero entries strictly increase a key, has at most rank N elements.
- `card_S_2_3_2`: at (r, Q, R) = (2, 3, 2), |S| = 7.

All four use only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Controls (`lean/controls/`):

- `must-pass.lean`: with the support condition weakened to mismatch ≤ R, the conclusion is false. At (r, Q, R) = (2, 1, 1), M = I is allowed and rank(I − M) = 0, but |S| = 1. It also restates |S| = 7 at (2, 3, 2) and prints the axioms.
- `must-fail.lean`: the theorem with the weakened condition, and the (2, 3, 2) count stated as 8. Lean must reject both.

Not in Lean:

- The probability form of the theorem and its e^{−Θ(R²/Q)} asymptotics, and their constants.
- That the paper's M₀ satisfies (2.14)/(4.4). This is taken from the paper.
- That the bound on measurement rows caps the running-time exponent of the main-text route. That needs an elimination over the route's other parameters, through the paper's (3.16), (4.10) and (4.15). Two of the models consulted argued it on paper; it was not checked here.
- **The swap-span statement.** A matrix in the span of products of swaps (Π_s exchanges a(s) and d(s)) satisfies the support condition exactly when M = Σ_{|T|<R} γ_T Π_{[Q]∖T}. On a joint eigenvector with signs σ it acts as (Π_s σ_s)·P(σ) with deg P < R, so rank(I − M)/D = Pr_σ[P(σ) ≠ Π_s σ_s], with each σ_s = −1 with probability (r−1)/2r. Restricting to a random fair subcube and counting dimensions as in Smolensky's argument gives rank(I − M)/D ≥ Pr[Σ_s Z_s ≥ R] with Pr[Z = ±1] = (r−1)/2r. This was proved on paper only. Stated as a bare e^{−O(R²/Q)} it is false for R = o(√Q); R = 1 is a counterexample.
- **The optimum 8 at (2, 3, 2).** That no matrix with the pattern does better than 8 rests on `scripts/mais.py`, an exhaustive search; that 8 is reached rests on `scripts/tiny.py`.

## The tiny case (r, Q, R) = (2, 3, 2), D = 64

By exact rational arithmetic:

| | rank(I − M) | how |
|---|---|---|
| best matrix in the swap span | 10 | every agreement set of an affine g enumerated; `tiny.py` |
| block-adapted matrix (interval chosen per block of unequal coordinates) | 8 | `tiny.py` |
| the set S | 7 | forced-diagonal and acyclic; `mais.py`, and `card_S_2_3_2` in Lean |
| largest forced-diagonal acyclic set | 8 | exhaustive; `mais.py` |

So the optimum over all matrices with the pattern is exactly 8, and S is not the largest triangular set: the theorem is a lower bound and is not tight. `mais.py` also checks (2, 2, 2) and (2, 3, 3), where S and the largest acyclic set both have one element. The scripts print the set S as "Opus's set". Their output is `results/out.txt`.

## What it does not cover

- A different auxiliary index set than B.
- Schedules that never use the labels in S.
- Measurement matrices that vary with the evaluation point.
- Appendix D of the paper, the tensor route that gives its headline bound.
- Anthropic's route: "A 2^{o(n)} time algorithm for 3-SAT" (26 October 2026; `github.com/anthropics/formal-math`, file `eth/paper.pdf`) and its recursion.

## How it was found

On 23 November 2026, at Ko Vial's suggestion, Claude (Fable 5.2) put one brief, on how far the October ETH algorithms can be pushed, to three models, each working alone: Claude Opus 5.5, GPT 6.2 Astra and Gemini 4 Neon. Each came back asking whether the square root in the saving is forced. Claude Opus claimed it is forced inside the swap span, and the other two were asked to referee that claim from the paper, without seeing a proof.

- Writing its claim out, Claude Opus proved the general bound.
- Refereeing, Gemini Neon proved the same bound with the same set S.
- Refereeing, GPT Astra found the block-adapted matrix that reaches 8 at (2, 3, 2).
- All three proved the swap-span statement.

Claude ran the consult, read both proofs of the general bound, wrote the scripts that check the (2, 3, 2) case, and formalized the theorem in Lean.

## Novelty

We did not find the bound in what we read on 23 November 2026, and that is weak evidence: a statement can be known to specialists without being written down, and each source was read once.

What was read: every post and comment on `ethdiscussion.blog`, the review site run by Impagliazzo, Paturi and Williams; O'Donnell's exposition (30 October); Sellke's slides; parts of Kintali's exposition and of the OpenAI paper. arXiv 2611.00517 (Dias, Lima) in full, 2611.09764 (Vassilevska Williams, Zamir) in large part, and 2611.11832, 2610.41622 and 2611.05082 skimmed; 21 arXiv searches for 26 October to 23 November; ECCC TR26-270 to TR26-337. None gives a lower bound on rank(I − M₀), on the number of measurements, or on R in terms of Q.

- Closest: O'Donnell §5.1, "exact niceness forces degree at least ℓ", which is the zero-rank extreme only.
- Dias and Lima §9 leave open "a bound for groups with several measurement rows". This theorem is a bound of that kind, for this support pattern only.
- The triangular-minor argument itself is standard.

Not read: O'Donnell's video lectures, and several notes shared only as Google Drive folders.

## Reproduce

Use Linux on x86-64 (tested) or arm64 (untested). You need bash, curl, git, python3 ≥ 3.9 (standard library only), zstd and tar, and about 6 GB of disk.

```
./reproduce.sh
```

It downloads the Lean 4.33.1 release tarball (checked by sha256), Mathlib and its dependencies (a shallow git fetch of each exact commit in `lean/lake-manifest.json`), and Mathlib's compiled cache (`lake exe cache get`, which picks files by the hashes of the pinned sources). Then it:

1. builds `lean/RankBarrier.lean`;
2. runs `controls/must-pass.lean`, prints the axioms of its five theorems and fails unless all are within the standard three;
3. runs `controls/must-fail.lean` and fails unless Lean rejects exactly its two statements, each with the expected error;
4. runs `scripts/tiny.py` and `scripts/mais.py` and fails unless their output equals `results/out.txt`.

Work files go to `./work` (or `$ERB_WORK`), Mathlib to `lean/.lake`.

**In Docker**, as tested on x86-64:

```
docker build -t eth-rank-barrier - <<'EOF'
FROM ubuntu:24.04@sha256:68ee22004a9109b44973313b02ff7b1de250f1de0f5ecb628d73f579aaff33ac
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
      ca-certificates curl git python3 zstd && rm -rf /var/lib/apt/lists/*
EOF
docker run --rm --memory 10g --cpus 2 -v "$PWD":/src:ro eth-rank-barrier \
  bash -c 'cp -a /src /pkg && /pkg/reproduce.sh'
```

On 23 November 2026 this took 1 min 54 s end to end in that container (2 CPUs), most of it downloading Mathlib's cache.

## Pins

- Lean `v4.33.1` (`lean/lean-toolchain`); release tarball sha256 at the top of `reproduce.sh`.
- Mathlib `v4.33.1`, commit `0df444a360eaa60ab8c11dca51a86af692955474`, and its dependencies at the commits in `lean/lake-manifest.json`.
- Python 3, standard library only.

## Layout

- `reproduce.sh`: fetch, build and check, as above.
- `lean/`: the Lake project. `RankBarrier.lean` is the proof; `controls/` holds the two controls.
- `scripts/tiny.py`: the swap-span optimum and the block-adapted matrix at (2, 3, 2). `scripts/mais.py r Q R`: the set S and the largest forced-diagonal acyclic set.
- `results/out.txt`: the scripts' output.

## License

Apache License 2.0; see `LICENSE`. Mathlib is downloaded under its own license, not included.
