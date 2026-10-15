import PanelMoments.SourceFamily
import PanelMoments.MomentLifts
import PanelMoments.SourceCounting

/- This checks general validity, lifts and index counts, not source independence. -/

#check PanelMoments.PermutationMoments.sourceMoment_isMoment
#check PanelMoments.SourceFamily.SourceIndex
#check PanelMoments.SourceFamily.sourceMoment_isMoment
#check PanelMoments.MomentLifts.firstStateLift_isMoment
#check PanelMoments.MomentLifts.linearIndependent_firstStateLift
#check PanelMoments.SourceCounting.card_sourceIndex_succ
#check PanelMoments.SourceCounting.five_period_source_count
#check PanelMoments.SourceCounting.six_period_source_count

example (N : ℕ) : Fintype (PanelMoments.SourceFamily.SourceIndex N) := inferInstance

#print axioms PanelMoments.PermutationMoments.likelihood_prefix_sum
#print axioms PanelMoments.PermutationMoments.scaleRatio_mul_likelihood
#print axioms PanelMoments.PermutationMoments.sharedPrefix_weightedChain_sum
#print axioms PanelMoments.PermutationMoments.contrast_isMoment
#print axioms PanelMoments.PermutationMoments.sourceMoment_isMoment
#print axioms PanelMoments.PermutationMoments.map_sourceNumerator
#print axioms PanelMoments.SourceFamily.coreList_nodup
#print axioms PanelMoments.SourceFamily.coreList_length
#print axioms PanelMoments.SourceFamily.orders_sharedPrefix
#print axioms PanelMoments.SourceFamily.orders_diverge
#print axioms PanelMoments.SourceFamily.sourceNumerator_eq_permutationNumerator
#print axioms PanelMoments.SourceFamily.sourceMoment_eq_permutationMoment
#print axioms PanelMoments.SourceFamily.map_sourceNumerator
#print axioms PanelMoments.SourceFamily.sourceMoment_isMoment
#print axioms PanelMoments.MomentLifts.firstStateLift_injective
#print axioms PanelMoments.MomentLifts.firstStateLift_isMoment
#print axioms PanelMoments.MomentLifts.linearIndependent_firstStateLift
#print axioms PanelMoments.SourceCounting.sharedSet_decomposition
#print axioms PanelMoments.SourceCounting.card_le_one_of_no_initial
#print axioms PanelMoments.SourceCounting.card_sizedShared_pos
#print axioms PanelMoments.SourceCounting.card_secondSlot
#print axioms PanelMoments.SourceCounting.card_sourceIndex_sum
#print axioms PanelMoments.SourceCounting.card_sourceIndex_recurrence
#print axioms PanelMoments.SourceCounting.card_sourceIndex_add_choose_of_ge_two
#print axioms PanelMoments.SourceCounting.card_sourceIndex
#print axioms PanelMoments.SourceCounting.card_sourceIndex_succ
#print axioms PanelMoments.SourceCounting.five_period_source_count
#print axioms PanelMoments.SourceCounting.six_period_source_count
