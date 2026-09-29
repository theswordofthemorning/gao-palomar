module

public import GaoCoalescence.GaoLiteral

@[expose] public section

/-!
# Proved solution

The proof lives in the modules under `GaoCoalescence/`, whose final statements
are `GaoEnunciado.conjetura_gao` (Lagarias's form) and
`GaoLiteral.conjetura_gao_literal` (Gao's form). This file restates the
definitions of `Challenge.lean` verbatim and bridges them to those theorems.
-/

open Filter Topology

namespace GaoCoalescence

/-- The Collatz map on `ℕ`: `n / 2` if `n` is even, `3n + 1` if `n` is odd. -/
def collatz (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `halvings k n` is the number of halvings among the first `k` steps of the
trajectory of `n`, that is, the number of even terms among
`n, C(n), …, C^(k-1)(n)`. -/
def halvings : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => (if n % 2 = 0 then 1 else 0) + halvings k (collatz n)

/-- Gao's coalescence of `n` and `n + 1` at step `k`: the trajectories agree at
step `k`, have the same number of halvings in their first `k` steps, and
neither of them contains `1` among its terms of index `0, …, k`. -/
def Coalesce (n k : ℕ) : Prop :=
  collatz^[k] n = collatz^[k] (n + 1) ∧ halvings k n = halvings k (n + 1) ∧
    ∀ i, i ≤ k → collatz^[i] n ≠ 1 ∧ collatz^[i] (n + 1) ≠ 1

open Classical in
/-- Gao's `d̄_k`: the number of `0 ≤ n < 2^k - 1` such that `n` and `n + 1`
coalesce at some step `j ≤ k`, divided by `2^k`. -/
noncomputable def dbar (k : ℕ) : ℝ :=
  (((Finset.range (2 ^ k - 1)).filter (fun n => ∃ j, j ≤ k ∧ Coalesce n j)).card : ℝ) / 2 ^ k

open Classical in
/-- Gao's `d(x)`: the proportion of `0 ≤ n < x` such that `n` and `n + 1`
coalesce at some step, with no bound on the step. -/
noncomputable def d (x : ℕ) : ℝ :=
  (((Finset.range x).filter (fun n => ∃ j, Coalesce n j)).card : ℝ) / x

theorem collatz_eq : collatz = Hienas.C := rfl

theorem halvings_eq : halvings = Hienas.mitades := by
  funext k
  induction k with
  | zero => funext n; rfl
  | succ k ih => funext n; simp only [halvings, Hienas.mitades, ih, collatz_eq]

theorem coalesce_eq : Coalesce = Hienas.coalescen := by
  funext n k
  simp only [Coalesce, Hienas.coalescen, halvings_eq, collatz_eq]

theorem dbar_eq : dbar = Hienas.dbarra := by
  funext k
  simp only [dbar, Hienas.dbarra, coalesce_eq]

theorem d_eq : d = Hienas.d := by
  funext x
  simp only [d, Hienas.d]
  congr
  exact congrArg (fun P : ℕ → ℕ → Prop => fun n => ∃ j, P n j) coalesce_eq

open Classical in
/-- **Gao's conjecture, in Lagarias's form.** The set of `m` such that
`C^k(m) = C^k(m + 1)` for some `k ≤ log₂ m` has natural density one. -/
theorem lagarias_form :
    Tendsto (fun N : ℕ => (((Finset.range N).filter
      (fun m => ∃ k, k ≤ Nat.log 2 m ∧ collatz^[k] m = collatz^[k] (m + 1))).card : ℝ) / N)
      atTop (𝓝 1) := by
  convert GaoEnunciado.conjetura_gao using 7
  exact Iff.rfl

/-- **Gao's conjecture, in Gao's form.** `d̄_k → 1`; moreover `d(x) → 1`. -/
theorem gao_form : Tendsto dbar atTop (𝓝 1) ∧ Tendsto d atTop (𝓝 1) := by
  rw [dbar_eq, d_eq]
  exact GaoLiteral.conjetura_gao_literal

end GaoCoalescence
