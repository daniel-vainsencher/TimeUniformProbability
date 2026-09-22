# Potential homes for this formalization

This repo (GitHub: daniel-vainsencher/TimeUniformProbability) currently carries a clean,
sorry-free proof of Ville's inequality for nonnegative supermartingales, verified against
mathlib at tag `master-2026-09-17` (see `lakefile.toml`). This file records candidate
venues for contributing it, and what each would require. Status: under consideration,
nothing submitted anywhere.

## Prior art: mathlib PRs (all closed, unmerged)

Three mathlib PRs formalized Ville's inequality in 2026; none was merged.

- PR #36641 (closed 2026-03-17): lacked a supremum-deviation statement, so reviewers
  judged it not really Ville's inequality. Author confirmed LLM (Claude) assistance.
- PR #37121 (closed 2026-04-17): closed by triage with an explicit message that the
  LLM-generated code failed to meet mathlib's standards.
- PR #40085 (closed 2026-06-01, discussed on Zulip, channel mathlib4, topic
  "Ville's Inequality"): mathematically sound; rejection was about AI policy, not content.

Lessons for any mathlib attempt:

- A submission must state the deviation of a (finite or countable) supremum, not just
  stopped-value bounds.
- The mathlib-idiomatic shape is the statement-for-statement dual of Doob's
  `MeasureTheory.maximal_ineq`: threshold `epsilon : RR>=0`, event written with
  `(range (n+1)).sup'`, form `epsilon * mu{...} <= ENNReal.ofReal (mu[f 0])`.
- Worth including: finite-horizon and probability-normalized (`mu[f 0] <= 1`, so
  `P <= alpha`) corollaries, the sequential-analysis forms.
- AI contribution policy applies and is enforced in triage.

PR #40085 (file saved at /tmp/pr40085_Ville.lean during the 2026-09 comparison) is a
useful statement checklist regardless of venue.

## lean-pool (Vilin97/lean-pool)

A pool of completed Lean 4 formalizations positioned between mathlib and merely-true:
213 projects, 3.2M lines. Explicitly uses LLM review (deterministic linters plus LLM
judgment) instead of mathlib's human-review bar.

Intake gates: builds warning-free on latest mathlib, passes mathlib linters and style
checks, no `sorry`/`admit`, no axioms beyond `Classical.choice`/`propext`/`Quot.sound`,
no `unsafe`/`partial`, permissive license (Apache-2.0 or MIT), proper file headers.

Readiness of this repo: the ported `Ville.lean` already meets the axiom and sorry gates
(verified via `#print axioms`); remaining work is the copyright-header lint and re-pinning
to lean-pool's mathlib version at submission time. Projects are added as whole repos via
the candidate queues in `candidates/` of that repository.

## Tau Ceti (TauCetiProject/TauCeti, roadmap at TauCetiProject/TauCetiRoadmap)

A Lean 4 library downstream of mathlib where AIs write and maintain the code under
adversarial review, incubated by the Lean FRO and the Mathlib Initiative. Humans own
scope: contributions land only in areas covered by a roadmap README in TauCetiRoadmap,
and roadmap changes are human-reviewed PRs there.

No existing roadmap covers supermartingale maximal inequalities. The closest is
"Exchangeability and de Finetti", which lists `TauCeti/Probability/Martingale/` as a
suggested home and builds reverse-martingale infrastructure, but its milestones are
de Finetti-focused and do not include Ville's inequality.

Contributing Ville's inequality to Tau Ceti therefore requires writing a roadmap first:
a markdown README specifying the area, plus `Suggested.lean` target signatures, accepted
by TauCetiRoadmap maintainers. The natural scope, per the intended direction toward
material useful for ML theory:

- Nonnegative supermartingales and Ville's inequality (this repo's core).
- Test supermartingales, e-values, and e-processes (ramdas et al. line of work).
- Time-uniform confidence sequences.
- The unified time-uniform PAC-Bayes recipe (Chugg, Mishler, Ramdas 2023).
- Sub-psi and CGF-like tail bounds feeding the above (already drafted on the local
  branch `daniel/wip-cgf-like`).

This complements the Exchangeability roadmap (which needs forward martingale
infrastructure from mathlib) rather than overlapping it.

## Positioning

lean-pool and Tau Ceti are not mutually exclusive. lean-pool takes the completed
artifact quickly; a TauCetiRoadmap proposal seeds a broader ML-theory probability area.
A future mathlib PR remains possible but requires human authorship with honest AI-use
disclosure, and a statement set at least as strong as PR #40085's.
