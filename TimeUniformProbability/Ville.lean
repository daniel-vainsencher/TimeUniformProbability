import Mathlib.Probability.Martingale.OptionalStopping
--import Mathlib.MeasureTheory
import Mathlib
/-!
# Ville's Inequality

This file formalizes Ville's inequality: for a nonneg supermartingale `(Lₙ)`,
  `P(∃ n, Lₙ ≥ a | F₀) ≤ L₀ / a`

## Proof route

Following Howard, Ramdas, McAuliffe, Sekhon (2020), arXiv:1808.03204, Section 2.2.
The proof is elementary and does NOT go through Doob's maximal inequality.

Step 1 (done): Supermartingale optional stopping —
  `Supermartingale.expected_stoppedValue_mono`
  If `f` is a supermartingale and `τ ≤ π` are bounded stopping times,
  then `μ[stoppedValue f π] ≤ μ[stoppedValue f τ]`.
  Proof: negate to get a submartingale, apply
  `Submartingale.expected_stoppedValue_mono`, flip.

Step 2 (TODO): Ville's inequality —
  Let τ := inf{t : Lₜ ≥ a} (hitting time, possibly ∞).
  For fixed m, `{τ ≤ m} = {∃ k ≤ m, Lₖ ≥ a}`.
  On this event, `Lτ∧m ≥ a`, so by Markov:
    `P(τ ≤ m) = P(Lτ∧m ≥ a) ≤ E[Lτ∧m] / a`
  By Step 1 with stopping times `(0 : ℕ)` and `τ ∧ m`:
    `E[Lτ∧m] ≤ E[L₀]`
  So `P(τ ≤ m) ≤ E[L₀] / a` for all m.
  Take m → ∞ via `MeasureTheory.tendsto_measure_iUnion`:
    `P(τ < ∞) = P(∃ n, Lₙ ≥ a) ≤ E[L₀] / a`

## Key Mathlib pieces needed for Step 2

* `MeasureTheory.hittingBtwn` — the hitting time `τ` between n and m
* `IsStoppingTime.min_const` — `τ ∧ m` is a stopping time
* `MeasureTheory.isStoppingTime_hitting` — `τ` is a stopping time
* `mul_meas_ge_le_lintegral₀` or `mul_meas_ge_le_integral_of_nonneg` — Markov's inequality
* `MeasureTheory.tendsto_measure_iUnion` — continuity of measure from below

## References

* Howard, Ramdas, McAuliffe, Sekhon (2020), arXiv:1808.03204, Theorem 1 / eq. (6.1)
* Mathlib: `MeasureTheory.Submartingale.expected_stoppedValue_mono`
* Mathlib: `MeasureTheory.maximal_ineq` (not used here)
-/

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {τ π : Ω → ℕ∞}

/-! ## Step 1: Supermartingale optional stopping -/

-- Belongs in Mathlib/Probability/Process/Stopping.lean alongside `stoppedValue_const`.
-- The [Nonempty ι] hypothesis may be droppable.
@[simp]
theorem stoppedValue_neg {ι} [Nonempty ι] {β : Type*} [Neg β]
    (u : ι → Ω → β) (τ : Ω → WithTop ι) :
    stoppedValue (-u) τ = -stoppedValue u τ := rfl

/-- For a supermartingale `f` and bounded stopping times `τ ≤ π`, the expectation of
`stoppedValue f` is *decreasing*: `E[f stopped at π] ≤ E[f stopped at τ]`.

This is the supermartingale analog of `Submartingale.expected_stoppedValue_mono`.
Proof: `-f` is a submartingale (`Supermartingale.neg`); apply the submartingale version;
negate both sides. -/
theorem Supermartingale.expected_stoppedValue_mono [SigmaFiniteFiltration μ 𝒢]
    (hf : Supermartingale f 𝒢 μ)
    (hτ : IsStoppingTime 𝒢 τ) (hπ : IsStoppingTime 𝒢 π) (hle : τ ≤ π)
    {N : ℕ} (hbdd : ∀ ω, π ω ≤ N) :
    μ[stoppedValue f π] ≤ μ[stoppedValue f τ] := by
  have h : ∫ (x : Ω), stoppedValue (-f) τ x ∂μ ≤ ∫ (x : Ω), stoppedValue (-f) π x ∂μ :=
    hf.neg.expected_stoppedValue_mono hτ hπ hle hbdd
  simp [stoppedValue_neg, integral_neg] at h
  linarith

/-! ## Step 2: Ville's inequality -/

/-- **Ville's inequality**: For a nonneg supermartingale `f` and threshold `a > 0`,
the probability that `f` ever reaches `a` is bounded by `E[f 0] / a`.

Formally: `μ {ω | ∃ n, a ≤ f n ω} ≤ ENNReal.ofReal (μ[f 0] / a)`

Proof sketch (Howard et al. 2020, eq. 6.1):
- For each `m : ℕ`, let `τ m ω := hittingBtwn f {x | a ≤ x} 0 m ω`
  (first time before `m` that `f` reaches `a`)
- For each `m : ℕ`, on the event `{τ < m}` we have `f τ ω ≥ a`
- Markov: `P(τ < m) ≤ P(f τ ≥ a) ≤ E[f (τ ∧ m)] / a`
- Optional stopping (Step 1): `E[f (τ ∧ m)] ≤ E[f 0]`
- So `P(τ ≤ m) ≤ E[f 0] / a` for all m
- `{∃ n, f n ω ≥ a} = {τ < ∞} = ⋃ m, {τ ≤ m}`, take m → ∞ -/
theorem Supermartingale.ville [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝒢]
    (hf : Supermartingale f 𝒢 μ) (hnonneg : 0 ≤ f) {a : ℝ} (ha : 0 < a) :
    μ {ω | ∃ n, a ≤ f n ω} ≤ ENNReal.ofReal (μ[f 0] / a) := by
    let τ : ℕ → Ω → ℕ := fun m ω => hittingBtwn f {x | a ≤ x} 0 m ω
    have hhit : ∀ m : ℕ, ∀ ω : Ω, τ m ω < m → a ≤ f (τ m ω) ω := by
      intro m ω hlt
      exact hittingBtwn_mem_set_of_hittingBtwn_lt hlt
    have hb : ∀ m : ℕ, μ.real { ω | τ m ω < m} ≤ μ.real { ω | f (τ m ω) ω ≥ a} := by
      intro m
      apply measureReal_mono
      · intro ω hω
        exact hhit m ω hω
      · exact measure_ne_top μ _
    have hc : ∀ m : ℕ, a * μ.real { ω | f (τ m ω) ω ≥ a } ≤ ∫ ω, f (τ m ω) ω ∂μ := by
      intro m
      have hint : Integrable (stoppedValue f (fun ω => (τ m ω : ℕ∞))) μ := by
        have h := hf.neg.integrable_stoppedValue
          (hf.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici)
          (fun ω => show (τ m ω : ℕ∞) ≤ (m : ℕ∞) from mod_cast hittingBtwn_le ω)
        have h' : Integrable (-stoppedValue f (fun ω => (τ m ω : ℕ∞))) μ := by
          convert h using 2
        simpa using h'.neg
      have heq : (fun ω => f (τ m ω) ω) = stoppedValue f (fun ω => (τ m ω : ℕ∞)) := rfl
      rw [heq]
      exact mul_meas_ge_le_integral_of_nonneg
        (ae_of_all μ (fun ω => hnonneg (τ m ω) ω)) hint a
    have hd : ∀ m : ℕ, μ[stoppedValue f (fun ω => (τ m ω : ℕ∞))] ≤ μ[f 0] := by
      intro m
      have hτ : IsStoppingTime 𝒢 (fun ω => (τ m ω : ℕ∞)) :=
        hf.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
      have h0 : IsStoppingTime 𝒢 (fun _ => (0 : ℕ∞)) := isStoppingTime_const 𝒢 0
      rw [← stoppedValue_const f 0]
      exact Supermartingale.expected_stoppedValue_mono hf h0 hτ
        (fun ω => zero_le _)
        (fun ω => mod_cast hittingBtwn_le ω)
    -- Per-m bound: μ {τ m ω < m} ≤ ENNReal.ofReal (μ[f 0] / a)
    have hbd : ∀ m : ℕ, μ { ω | τ m ω < m } ≤ ENNReal.ofReal (μ[f 0] / a) := by
      intro m
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
      apply ENNReal.ofReal_le_ofReal
      have key : a * μ.real { ω | τ m ω < m } ≤ μ[f 0] :=
        calc a * μ.real { ω | τ m ω < m }
            ≤ a * μ.real { ω | f (τ m ω) ω ≥ a } :=
              mul_le_mul_of_nonneg_left (hb m) ha.le
          _ ≤ ∫ ω, f (τ m ω) ω ∂μ := hc m
          _ = μ[stoppedValue f (fun ω => (τ m ω : ℕ∞))] := rfl
          _ ≤ μ[f 0] := hd m
      have key' : μ.real {ω | τ m ω < m} * a ≤ μ[f 0] := by
        linarith [mul_comm a (μ.real {ω | τ m ω < m})]
      exact (le_div_iff₀ ha).mpr key'
    -- The target set equals the union of {τ m ω < m}
    have hset : { ω | ∃ n, a ≤ f n ω } = ⋃ m, { ω | τ m ω < m } := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨n, hn⟩
        refine ⟨n + 1, ?_⟩
        change hittingBtwn f {x | a ≤ x} 0 (n + 1) ω < n + 1
        exact lt_of_le_of_lt
          (hittingBtwn_le_of_mem (u := f) (s := {x | a ≤ x}) (Nat.zero_le n) (Nat.le_succ n) hn)
          (Nat.lt_succ_self n)
      · rintro ⟨m, hm⟩
        exact ⟨τ m ω, hhit m ω hm⟩
    -- Monotonicity of the sets
    have hmono : Monotone (fun m => { ω : Ω | τ m ω < m }) := by
      intro p q hpq ω hω
      simp only [Set.mem_setOf_eq] at *
      -- τ p ω fires before p, so τ q ω ≤ τ p ω < p ≤ q
      have hmem : f (τ p ω) ω ∈ ({x | a ≤ x} : Set ℝ) :=
        hittingBtwn_mem_set_of_hittingBtwn_lt hω
      have hle : τ q ω ≤ τ p ω :=
        hittingBtwn_le_of_mem (Nat.zero_le _) (hω.le.trans hpq) hmem
      omega
    -- Apply continuity of measure from below and bound each term
    rw [hset]
    apply le_of_tendsto (tendsto_measure_iUnion_atTop hmono)
    exact Filter.eventually_atTop.mpr ⟨0, fun m _ => hbd m⟩
