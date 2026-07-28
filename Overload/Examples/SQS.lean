import Mathlib
import Overload.Deadline
import Overload.Amplification
import Overload.Bistability
import Overload.Priority

/-!
# Example: an SQS-style redelivery queue

A message queue in the style of AWS SQS, from public documented semantics: a
consumer receives a message, which becomes invisible for the **visibility
timeout** `τᵥ`; if the consumer fails to delete it in time, the queue makes it
visible again and redelivers. Redelivery repeats until the message's
**retention period** `D` expires, or until a **redrive policy** moves it to a
dead-letter queue after `maxReceiveCount` receives.

The mapping into this library, and the point of the example:

* The visibility timeout is a **re-armed per-try sub-deadline** — sustaining
  mechanism 2 — enforced by the *server*. The
  retry loop lives in the architecture: there is **no client retry code
  anywhere**, and the amplification is pure configuration.
* At the public defaults (`τᵥ = 30 s`, retention 4 days) an always-failing
  message is delivered `⌊345600/30⌋ = 11520` times — the first delivery plus
  11519 redeliveries (`sqs_redelivery_cap`). With that amplification, one
  message per second of poisoned traffic sustains a congested equilibrium
  against a consumer fleet one hundred times faster
  (`sqs_unclamped_bistable`, `sqs_unclamped_congestedEq`).
* A redrive policy is exactly the **cap clamp**: `maxReceiveCount = 5`
  with offered poison load `λ` satisfying `λ·5 < C` removes the congested
  equilibrium outright (`sqs_dlq_no_congestedEq`) — no timing, backoff, or
  kernel assumptions. The honest residual: the clamp does not close the band.
  At `λ = 25` against `C = 100` the clamped system itself is genuinely
  bistable (`sqs_dlq_band_residual`, certified directly on `dlqLoop` by the
  two-point certificate) — one point, not the whole interval.
  `sqs_dlq_band_lower` runs the other direction only: a congested
  equilibrium under the clamp forces `λ ≥ C/5`, which is necessary for
  collapse and not sufficient for it. Either way the dead-letter queue is a
  mitigation with a stated boundary, not a cure.
* Two workloads sharing one consumer fleet contend by *attempt* volume, not by
  intent: a bulk workload at half the interactive rate but redelivering
  30× takes 15× the goodput under storm (`sqs_bulk_outranks`), and for any
  target share there is a redelivery amplification that starves the
  interactive class below it (`sqs_inversion_instance`).

Numbers are AWS public defaults where noted (30 s visibility timeout, 4-day
default retention) and stylized otherwise (capacities, rates, the
`maxReceiveCount = 5` redrive choice). The claims are about the *arithmetic
of the configuration*, not measurements of the service.
-/

namespace Overload

/-!
## Redelivery arithmetic: the visibility timeout as a re-armed sub-deadline
-/

/-- **11520 deliveries by default.** A message that consistently fails
processing, under a 30 s visibility timeout and the default 4-day (345600 s)
retention with no redrive policy (cap shown: 20000, i.e. effectively
unbounded), is delivered 11520 times — the first delivery plus 11519
redeliveries. The deadline arithmetic of `Deadline.lean`, with the *server* re-arming
the sub-deadline. -/
theorem sqs_redelivery_cap :
    neff (fun _ => (30 : ℝ)) (fun _ => 0) 345600 20000 = 11520 := by
  rw [neff_rearmed (by norm_num) (by norm_num)]
  norm_num

/-!
## The unclamped loop: bistable at one message per second

The stylized closed loop: poisoned offered load `λ = 1` msg/s, consumer fleet
capacity `C = 100` msg/s, saturated redelivery amplification `A = 11520`.
-/

/-- The unclamped redelivery loop: poisoned load 1 msg/s, fleet capacity
100 msg/s, saturated redelivery amplification 11520. -/
noncomputable abbrev sqsUnclampedLoop : ClosedLoop :=
  stepLoop 1 100 11520 (by norm_num) (by norm_num)

/-- With unbounded redelivery, the loop is **bistable**: the healthy
equilibrium (1 msg/s of load against a 100 msg/s fleet) and a congested
equilibrium coexist. A burst that tips the system into the congested basin
stays there after the burst ends. -/
theorem sqs_unclamped_bistable : BistableOn sqsUnclampedLoop.F 0 (1 * 11520) :=
  stepLoop_bistable (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The congested equilibrium of the unclamped loop is genuine: a
self-sustaining demand level at or above the fleet's capacity, fed entirely
by server-side redelivery of failing messages. -/
theorem sqs_unclamped_congestedEq : sqsUnclampedLoop.CongestedEq 100 :=
  stepLoop_congestedEq (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-!
## The redrive policy as the clamp
-/

/-- The redelivery loop under a redrive policy: the amplification response is
the truncated geometric at cap `m` (`maxReceiveCount`), over the saturated
step kernel — `Bistability.cappedLoop`, read as an SQS redrive policy. -/
noncomputable abbrev dlqLoop (lam C : ℝ) (m : ℕ) (hlam : 0 ≤ lam)
    (hm : 1 ≤ m) : ClosedLoop :=
  cappedLoop lam C m hlam hm

/-- **The dead-letter queue removes the congested equilibrium.** With
`maxReceiveCount = 5` and poison load 1 msg/s against a 100 msg/s fleet,
`λ·5 = 5 < 100` and no congested equilibrium exists — whatever the failure
kernel does, however failures are timed, with no backoff hypothesis anywhere.
One inequality certifies the architecture. -/
theorem sqs_dlq_no_congestedEq :
    ¬(dlqLoop 1 100 5 (by norm_num) (by norm_num)).CongestedEq 100 :=
  cappedLoop_no_congestedEq (by norm_num)

/-- **The honest residual**: the clamp does not close the band, it narrows it.
At `λ = 25` msg/s of poison load (inside `[C/5, C) = [20, 100)`), the
`maxReceiveCount = 5` system itself — the truncated-geometric `dlqLoop`, not
a stylized stand-in — is still genuinely bistable, certified by two point
evaluations of its own demand operator: `F(25) = 25` (healthy demand fixed)
and `F(100) = 125 ≥ 100` (congested demand self-sustaining). -/
theorem sqs_dlq_band_residual :
    BistableOn (dlqLoop 25 100 5 (by norm_num) (by norm_num)).F 0 125 := by
  refine (dlqLoop 25 100 5 (by norm_num)
      (by norm_num)).bistableOn_of_two_points
    (x := 25) (y := 100) (by norm_num) ?_ ?_ (by norm_num) ?_
  · rw [cappedLoop_F_of_lt (by norm_num)]
  · rw [cappedLoop_F_of_ge (by norm_num)]
    norm_num
  · show (25 : ℝ) * ((5 : ℕ) : ℝ) ≤ 125
    norm_num

/-- The band's lower edge, from the clamp: any congested equilibrium under
`maxReceiveCount = 5` against `C = 100` forces poison load `λ ≥ 20` msg/s.
Below that, the redrive policy is a full guarantee. -/
theorem sqs_dlq_band_lower {lam : ℝ} (hlam : 0 ≤ lam)
    (hcong : (dlqLoop lam 100 5 hlam (by norm_num)).CongestedEq 100) :
    20 ≤ lam := by
  have h := clamp_band_lower
    (dlqLoop lam 100 5 hlam (by norm_num)).toBoundedLoop
    (K := ((5 : ℕ) : ℝ)) (by norm_num)
    ((dlqLoop lam 100 5 hlam (by norm_num)).h_le_Amax) hcong
  norm_num at h
  exact h

/-!
## Two workloads, one fleet: contention by attempts, not intent
-/

/-- **Redelivery volume is effective priority.** An interactive workload at
2 msg/s that never retries, sharing a fleet with a bulk workload at 1 msg/s
whose messages are redelivered 30 times: under storm, the bulk workload takes
15× the interactive workload's goodput. The queue serves attempts; it never
sees intent. -/
theorem sqs_bulk_outranks {ρ : ℝ} (hρ : ρ ≠ 0) :
    sharedGoodput ![2, 1] ![1, 30] ρ 1 / sharedGoodput ![2, 1] ![1, 30] ρ 0
      = 15 := by
  rw [effective_priority ![2, 1] ![1, 30] hρ (i := 0) (j := 1)]
  norm_num [offeredAttempts]

/-- **The inversion, instantiated**: for the 1%-share target there is a bulk
redelivery amplification that drives the interactive workload (2 msg/s,
amplification 1) below 1% of total goodput. Nothing about intended priority
appears anywhere in the system. -/
theorem sqs_inversion_instance :
    ∃ Alo, 0 < Alo ∧ (2 * 1) / (2 * 1 + 1 * Alo) < (1 / 100 : ℝ) :=
  inversion (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Overload
