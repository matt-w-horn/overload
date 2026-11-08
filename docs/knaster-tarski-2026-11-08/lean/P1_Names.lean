import Mathlib.Order.FixedPoints
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Order.CompleteSublattice
import Mathlib.Order.Closure
import Mathlib.Order.Iterate
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.WithTop
import Mathlib.Order.WithBot
import Mathlib.Order.Interval.Set.ProjIcc
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Dynamics.FixedPoints.Topology
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Data.Set.Function

-- §3.1 exists?
#check @OrderHom.lfp
#check @OrderHom.prevFixed
#check @OrderHom.nextFixed
#check @OrderHom.nextFixed_le
#check @OrderHom.le_nextFixed
#check @fixedPoints.completeLattice
#check @fixedPoints.lfp_eq_sSup_iterate
#check @Set.Icc.completeLattice
#check @Set.Icc.coe_sSup
#check @Set.Icc.coe_sInf
#check @Subtype.isLUB_of_csSup_image_mem
#check @Subtype.isGLB_of_csInf_image_mem
#check @Set.OrdConnected.conditionallyCompleteLinearOrder
#check @CompleteSublattice
#check @ClosureOperator.ofPred
#check @ClosureOperator.eq_ofPred_closed
#check @ClosureOperator.ofCompletePred
#check @GaloisConnection.closureOperator
#check @ClosureOperator.le_closure
#check @ClosureOperator.idempotent
#check @ClosureOperator.closure_isGLB
#check @ClosureOperator.le_closure_iff
#check @ClosureOperator.closure_sup_closure
#check @ClosureOperator.isClosed_closure
#check @ClosureOperator.closure_min
#check @ClosureOperator.isClosed_iff_closure_le
#check @IsLeast.orderBot
#check @IsGreatest.orderTop
#check @Monotone.monotone_iterate_of_le_map
#check @Set.MapsTo.restrict
#check @Set.MapsTo.coe_iterate_restrict
#check @WithBot.monotone_map_iff
#check @Monotone.withBot_map
#check @WithTop.monotone_map_iff
#check @Monotone.withTop_map
#check @csSup_eq_csSup_of_forall_exists_le
#check @csInf_eq_csInf_of_forall_exists_le
#check (inferInstance : CompleteLattice (WithTop (WithBot ℝ)))
#check @WithTop.coe_sInf'
#check @WithBot.coe_sInf'
#check @WithTop.untop
#check @WithBot.unbot
#check @WithTop.coe_untop
#check @WithBot.coe_unbot
#check @tendsto_atTop_ciSup
#check @Function.isFixedPt_of_tendsto_iterate
#check @isFixedPt_of_tendsto_iterate
#check @isClosed_fixedPoints
#check @fixedPoints.iterateChain
#check @fixedPoints.ωSup_iterate_mem_fixedPoint
#check @fixedPoints.ωSup_iterate_le_prefixedPoint
#check @Set.projIcc
#check @Monotone.IccExtend
#check @exists_mem_Icc_isFixedPt
#check @exists_mem_Icc_isFixedPt_of_mapsTo
#check @OrderHom.coe_iterate
#check @Subtype.lattice

-- simps-generated names for ofPred / ofCompletePred
#check @ClosureOperator.ofPred_apply
#check @ClosureOperator.ofPred_isClosed
#check @ClosureOperator.ofCompletePred_apply
#check @ClosureOperator.ofCompletePred_isClosed

-- §3.3 "do not exist" — each of these should ERROR
#check @OrderHom.lfp_def
#check @OrderHom.gfp_def
#check @Set.MapsTo.restrict_iterate
#check @WithTop.map_mono
#check @WithBot.map_mono
#check @Set.MapsTo.restrictOrderHom
#check @OrderHom.iterate_bot_le_lfp
#check @OrderHom.gfp_le_iterate_top

-- §3.3 exact? probes
example {α : Type*} [CompleteLattice α] (f : α →o α) (n : ℕ) : f^[n] ⊥ ≤ f.lfp := by exact?
example {α : Type*} [CompleteLattice α] (f : α →o α) (n : ℕ) : f.gfp ≤ f^[n] ⊤ := by exact?
example {α : Type*} [Lattice α] (a b : α) : Monotone fun x : α ↦ (x ⊔ a) ⊓ b := by exact?

-- deprecated check
#check @subsetSupSet
