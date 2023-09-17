/-
Copyright (c) 2023 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner

/-!
# Integration of bounded continuous functions

In this file, some results are collected about integrals of bounded continuous functions. They are
mostly specializations of results in general integration theory, but they are used directly in this
specialized form in some other files, in particular in those related to the topology of weak
convergence of probability measures and finite measures.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction Topology

namespace BoundedContinuousFunction

section

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]

theorem NNReal.coe_ennreal_comp_measurable (f : X →ᵇ ℝ≥0) :
    Measurable fun x ↦ (f x : ℝ≥0∞) :=
  measurable_coe_nnreal_ennreal.comp f.continuous.measurable
#align bounded_continuous_function.nnreal.to_ennreal_comp_measurable BoundedContinuousFunction.NNReal.coe_ennreal_comp_measurable

variable (μ : Measure X) [IsFiniteMeasure μ]

theorem NNReal.lintegral_lt_top (f : X →ᵇ ℝ≥0) :
    (∫⁻ x, f x ∂μ) < ∞ := by
  apply IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal
  refine ⟨nndist f 0, fun x ↦ ?_⟩
  have key := BoundedContinuousFunction.Nnreal.upper_bound f x
  rwa [ENNReal.coe_le_coe]
#align measure_theory.lintegral_lt_top_of_bounded_continuous_to_nnreal BoundedContinuousFunction.NNReal.lintegral_lt_top

theorem NNReal.integrable (f : X →ᵇ ℝ≥0) :
    Integrable (((↑) : ℝ≥0 → ℝ) ∘ ⇑f) μ := by
  refine' ⟨(NNReal.continuous_coe.comp f.continuous).measurable.aestronglyMeasurable, _⟩
  simp only [HasFiniteIntegral, Function.comp_apply, NNReal.nnnorm_eq]
  exact lintegral_lt_top _ f
#align measure_theory.finite_measure.integrable_of_bounded_continuous_to_nnreal BoundedContinuousFunction.NNReal.integrable

/-
theorem integrable_of_boundedContinuous_to_real (f : X →ᵇ ℝ) :
    Integrable (⇑f) μ := by
  refine' ⟨f.continuous.measurable.aestronglyMeasurable, _⟩
  apply (hasFiniteIntegral_iff_norm f).mpr
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · exact ENNReal.ofReal_lt_top
  · exact MeasureTheory.FiniteMeasure.integrable_of_boundedContinuous_to_nnreal μ f.nnnorm
  · exact eventually_of_forall fun X => norm_nonneg (f X)
 -/

--#align measure_theory.finite_measure.integrable_of_bounded_continuous_to_real MeasureTheory.FiniteMeasure.integrable_of_boundedContinuous_to_real

theorem integral_eq_integral_nnrealPart_sub (f : X →ᵇ ℝ) :
    ∫ x, f x ∂μ = (∫ x, (f.nnrealPart x : ℝ) ∂μ) - ∫ ω, ((-f).nnrealPart ω : ℝ) ∂μ := by
  simp only [f.self_eq_nnrealPart_sub_nnrealPart_neg, Pi.sub_apply, integral_sub, NNReal.integrable]
  rfl
#align bounded_continuous_function.integral_eq_integral_nnreal_part_sub BoundedContinuousFunction.integral_eq_integral_nnrealPart_sub

theorem lintegral_lt_top_of_boundedContinuous_to_real (f : X →ᵇ ℝ) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) < ∞ := NNReal.lintegral_lt_top _ f.nnrealPart
#align measure_theory.finite_measure.lintegral_lt_top_of_bounded_continuous_to_real BoundedContinuousFunction.lintegral_lt_top_of_boundedContinuous_to_real

theorem NNReal.toReal_lintegral_eq_integral (f : X →ᵇ ℝ≥0)
    (μ : Measure X) : (∫⁻ x, (f x : ℝ≥0∞) ∂μ).toReal = ∫ x, (f x : ℝ) ∂μ := by
  rw [integral_eq_lintegral_of_nonneg_ae _ (by simpa [Function.comp_apply] using
        (NNReal.continuous_coe.comp f.continuous).measurable.aestronglyMeasurable)]
  · simp only [ENNReal.ofReal_coe_nnreal]
  · exact eventually_of_forall (by simp only [Pi.zero_apply, NNReal.zero_le_coe, imp_true_iff])
#align bounded_continuous_function.nnreal.to_real_lintegral_eq_integral BoundedContinuousFunction.NNReal.toReal_lintegral_eq_integral

end

section

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
variable (μ : Measure X)
variable {E : Type*} [NormedAddCommGroup E] [TopologicalSpace.SecondCountableTopology E]
variable [MeasurableSpace E] [BorelSpace E]

lemma lintegral_nnnorm_le [IsFiniteMeasure μ] (f : X →ᵇ E) :
    ∫⁻ x, ‖f x‖₊ ∂μ ≤ ‖f‖₊ * (μ Set.univ) := by
  calc  ∫⁻ x, ‖f x‖₊ ∂μ
    _ ≤ ∫⁻ _, ‖f‖₊ ∂μ         := ?_
    _ = ‖f‖₊ * (μ Set.univ)   := by rw [lintegral_const]
  · apply lintegral_mono -- NOTE: Would be great to have `gcongr` working for these.
    exact fun x ↦ ENNReal.coe_le_coe.mpr (nnnorm_coe_le_nnnorm f x)

lemma integrable [IsFiniteMeasure μ] (f : X →ᵇ E) :
    Integrable f μ := by
  refine ⟨f.continuous.measurable.aestronglyMeasurable, (hasFiniteIntegral_def _ _).mp ?_⟩
  calc  ∫⁻ x, ‖f x‖₊ ∂μ
    _ ≤ ‖f‖₊ * (μ Set.univ)   := f.lintegral_nnnorm_le μ
    _ < ∞                     := ENNReal.mul_lt_top ENNReal.coe_ne_top (measure_ne_top μ Set.univ)

variable [NormedSpace ℝ E]

lemma norm_integral_le_mul_norm [IsFiniteMeasure μ] (f : X →ᵇ E) :
    ‖∫ x, (f x) ∂μ‖ ≤ ENNReal.toReal (μ Set.univ) * ‖f‖ := by
  calc  ‖∫ x, (f x) ∂μ‖
    _ ≤ ∫ x, ‖f x‖ ∂μ                       := by exact norm_integral_le_integral_norm _
    _ ≤ ∫ _, ‖f‖ ∂μ                         := ?_
    _ = ENNReal.toReal (μ Set.univ) • ‖f‖   := by rw [integral_const]
  · apply integral_mono _ (integrable_const ‖f‖) (fun x ↦ f.norm_coe_le_norm x) -- NOTE: `gcongr`?
    exact (integrable_norm_iff f.continuous.measurable.aestronglyMeasurable).mpr (f.integrable μ)

lemma norm_integral_le_norm [IsProbabilityMeasure μ] (f : X →ᵇ E) :
    ‖∫ x, (f x) ∂μ‖ ≤ ‖f‖ := by
  convert f.norm_integral_le_mul_norm μ
  simp only [measure_univ, ENNReal.one_toReal, one_mul]

lemma bounded_range_integral
    {ι : Type*} (μs : ι → Measure X) [∀ i, IsProbabilityMeasure (μs i)] (f : X →ᵇ E) :
    Metric.Bounded (Set.range (fun i ↦ ∫ x, (f x) ∂ (μs i))) := by
  apply bounded_iff_forall_norm_le.mpr ⟨‖f‖, fun v hv ↦ ?_⟩
  obtain ⟨i, hi⟩ := hv
  rw [← hi]
  apply f.norm_integral_le_norm (μs i)

end

section

variable {X : Type*} [TopologicalSpace X]
variable [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

lemma BoundedContinuousFunction.integral_add_const (f : X →ᵇ ℝ) (c : ℝ) :
    ∫ x, (f + BoundedContinuousFunction.const X c) x ∂μ =
      ∫ x, f x ∂μ + ENNReal.toReal (μ (Set.univ)) • c := by
  simp [integral_add (f.integrable _) (integrable_const c)]

lemma BoundedContinuousFunction.integral_const_sub (f : X →ᵇ ℝ) (c : ℝ) :
    ∫ x, (BoundedContinuousFunction.const X c - f) x ∂μ =
      ENNReal.toReal (μ (Set.univ)) • c - ∫ x, f x ∂μ := by
  simp [integral_sub (integrable_const c) (f.integrable _)]

end

end BoundedContinuousFunction
