/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.NormedSpace.HahnBanach.SeparatingDual
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Rademacher's theorem: a Lipschitz function is differentiable almost everywhere

This file proves Rademacher's theorem: a Lipschitz function between finite-dimensional real vector
spaces is differentiable almost everywhere with respect to Lebesgue measure. This is the content
of `LipschitzWith.ae_differentiableAt`. Versions for functions which are Lipschitz on sets are also
given (see `LipschitzOnWith.ae_differentiableWithinAt`).

## Implementation

There are many proofs of Rademacher's theorem. We follow the one by Morrey, which is not the most
elementary but maybe the most elegant once necessary prerequisites are set up.
* Step 0: without loss of generality, one may assume that `f` is real-valued.
* Step 1: Since a one-dimensional Lipschitz function has bounded variation, it is differentiable
almost everywhere. With a Fubini argument, it follows that given any vector `v` then `f` is ae
differentiable in the direction of `v`. See `LipschitzWith.ae_lineDifferentiableAt`.
* Step 2: the line derivative `LineDeriv ℝ f x v` is ae linear in `v`. Morrey proves this by a
duality argument, integrating against a smooth compactly supported function `g`, passing the
derivative to `g` by integration by parts, and using the linearity of the derivative of `g`.
See `LipschitzWith.ae_lineDeriv_sum_eq`.
* Step 3: consider a countable dense set `s` of directions. Almost everywhere, the function `f`
is line-differentiable in all these directions and the line derivative is linear. Approximating
any direction by a direction in `s` and using the fact that `f` is Lipschitz to control the error,
it follows that `f` is Fréchet-differentiable at these points.
See `LipschitzWith.hasFderivAt_of_hasLineDerivAt_of_closure`.
-/

open Filter MeasureTheory Measure FiniteDimensional Metric Set

open scoped BigOperators NNReal ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {C D : ℝ≥0} {f g : E → ℝ} {s : Set E}
  {μ : Measure E} [IsAddHaarMeasure μ]

namespace LipschitzWith

/-!
### Step 1: A Lipschitz function is ae differentiable in any given direction

This follows from the one-dimensional result that a Lipschitz function on `ℝ` has bounded
variation, and is therefore ae differentiable, together with a Fubini argument.
-/

theorem ae_lineDifferentiableAt_of_prod
    {C : ℝ≥0} {f : E × ℝ → ℝ} (hf : LipschitzWith C f) {μ : Measure E} :
    ∀ᵐ p ∂(μ.prod volume), LineDifferentiableAt ℝ f p (0, 1) := by
  apply (ae_prod_mem_iff_ae_ae_mem (measurableSet_lineDifferentiableAt hf.continuous)).2
  apply eventually_of_forall (fun x ↦ ?_)
  have : ∀ᵐ (y : ℝ), DifferentiableAt ℝ (fun z ↦ f (x, z)) y := by
    apply LipschitzWith.ae_differentiableAt_real (C := C)
    intro z z'
    convert hf (x, z) (x, z')
    simp [Prod.edist_eq]
  filter_upwards [this] with y hy
  have h'y : DifferentiableAt ℝ (fun z ↦ f (x, z)) (y + 0) := by simpa using hy
  have : DifferentiableAt ℝ (fun t ↦ y + t) 0 :=
    (differentiable_id.const_add _).differentiableAt
  simpa only [LineDifferentiableAt, Prod.smul_mk, smul_zero, smul_eq_mul, mul_one, Prod.mk_add_mk,
    add_zero] using h'y.comp 0 this

theorem ae_lineDifferentiableAt (hf : LipschitzWith C f) (v : E) :
    ∀ᵐ p ∂μ, LineDifferentiableAt ℝ f p v := by
  rcases eq_or_ne v 0 with rfl|hv
  · simp [lineDifferentiableAt_zero]
  let n := finrank ℝ E
  let F := Fin (n-1) → ℝ
  obtain ⟨L, hL⟩ : ∃ L : (F × ℝ) ≃L[ℝ] E, L (0, 1) = v := by
    have : Nontrivial E := nontrivial_of_ne v 0 hv
    have M : (F × ℝ) ≃L[ℝ] E := by
      apply ContinuousLinearEquiv.ofFinrankEq
      simpa using Nat.sub_add_cancel finrank_pos
    obtain ⟨N, hN⟩ : ∃ N : E ≃L[ℝ] E, N (M (0, 1)) = v :=
      SeparatingDual.exists_continuousLinearEquiv_apply_eq (by simp) hv
    exact ⟨M.trans N, hN⟩
  let ρ : Measure (F × ℝ) := addHaar.prod volume
  have : IsAddHaarMeasure (Measure.map L ρ) := L.isAddHaarMeasure_map ρ
  suffices H : ∀ᵐ p ∂(Measure.map L ρ), LineDifferentiableAt ℝ f p v from
    absolutelyContinuous_isAddHaarMeasure _ _ H
  apply (ae_map_iff L.continuous.aemeasurable (measurableSet_lineDifferentiableAt hf.continuous)).2
  have : ∀ᵐ p ∂ρ, LineDifferentiableAt ℝ (f ∘ L) p (0, 1) :=
    (hf.comp L.lipschitz).ae_lineDifferentiableAt_of_prod
  filter_upwards [this] with p hp
  have h'p : LineDifferentiableAt ℝ (f ∘ (L : (F × ℝ) →ₗ[ℝ] E)) p (0, 1) := hp
  rw [← hL]
  exact LineDifferentiableAt.of_comp h'p

theorem memℒp_lineDeriv (hf : LipschitzWith C f) (v : E) :
    Memℒp (fun x ↦ lineDeriv ℝ f x v) ∞ μ :=
  memℒp_top_of_bound (aestronglyMeasurable_lineDeriv hf.continuous μ)
    (C * ‖v‖) (eventually_of_forall (fun _x ↦ norm_lineDeriv_le_of_lipschitz ℝ hf))

theorem locallyIntegrable_lineDeriv (hf : LipschitzWith C f) (v : E) :
    LocallyIntegrable (fun x ↦ lineDeriv ℝ f x v) μ :=
  (hf.memℒp_lineDeriv v).locallyIntegrable le_top

/-!
### Step 2: the ae line derivative is linear

Surprisingly, this is the hardest step. We prove it using an elegant but slightly sophisticated
argument by Morrey, with a distributional flavor: we integrate against a smooth function, and push
the derivative to the smooth function by integration by parts. As the derivative of a smooth
function is linear, this gives the result.
-/

theorem integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul
    (hf : LipschitzWith C f) (hg : Integrable g μ) (v : E) :
    Tendsto (fun (t : ℝ) ↦ ∫ x, (t⁻¹ • (f (x + t • v) - f x)) * g x ∂μ) (𝓝[>] 0)
      (𝓝 (∫ x, lineDeriv ℝ f x v * g x ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ (C * ‖v‖) * ‖g x‖)
  · apply eventually_of_forall (fun t ↦ ?_)
    apply AEStronglyMeasurable.mul ?_ hg.aestronglyMeasurable
    apply aestronglyMeasurable_const.smul
    apply AEStronglyMeasurable.sub _ hf.continuous.measurable.aestronglyMeasurable
    apply AEMeasurable.aestronglyMeasurable
    exact hf.continuous.measurable.comp_aemeasurable' (aemeasurable_id'.add_const _)
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    apply eventually_of_forall (fun x ↦ ?_)
    calc ‖t⁻¹ • (f (x + t • v) - f x) * g x‖
      = (t⁻¹ * ‖f (x + t • v) - f x‖) * ‖g x‖ := by simp [norm_mul, ht.le]
    _ ≤ (t⁻¹ * (C * ‖(x + t • v) - x‖)) * ‖g x‖ := by
      gcongr; exact LipschitzWith.norm_sub_le hf (x + t • v) x
    _ = (C * ‖v‖) *‖g x‖ := by field_simp [norm_smul, abs_of_nonneg ht.le]; ring
  · exact hg.norm.const_mul _
  · filter_upwards [hf.ae_lineDifferentiableAt v] with x hx
    exact hx.hasLineDerivAt.tendsto_nhdsWithin_right.mul tendsto_const_nhds

theorem integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul'
    (hf : LipschitzWith C f) (h'f : HasCompactSupport f) (hg : Continuous g) (v : E) :
    Tendsto (fun (t : ℝ) ↦ ∫ x, (t⁻¹ • (f (x + t • v) - f x)) * g x ∂μ) (𝓝[>] 0)
      (𝓝 (∫ x, lineDeriv ℝ f x v * g x ∂μ)) := by
  let K := cthickening (‖v‖) (tsupport f)
  have K_compact : IsCompact K := IsCompact.cthickening h'f
  apply tendsto_integral_filter_of_dominated_convergence
      (K.indicator (fun x ↦ (C * ‖v‖) * ‖g x‖))
  · apply eventually_of_forall (fun t ↦ ?_)
    apply AEStronglyMeasurable.mul ?_ hg.aestronglyMeasurable
    apply aestronglyMeasurable_const.smul
    apply AEStronglyMeasurable.sub _ hf.continuous.measurable.aestronglyMeasurable
    apply AEMeasurable.aestronglyMeasurable
    exact hf.continuous.measurable.comp_aemeasurable' (aemeasurable_id'.add_const _)
  · filter_upwards [Ioc_mem_nhdsWithin_Ioi' zero_lt_one] with t ht
    have t_pos : 0 < t := ht.1
    apply eventually_of_forall (fun x ↦ ?_)
    by_cases hx : x ∈ K
    · calc ‖t⁻¹ • (f (x + t • v) - f x) * g x‖
        = (t⁻¹ * ‖f (x + t • v) - f x‖) * ‖g x‖ := by simp [norm_mul, t_pos.le]
      _ ≤ (t⁻¹ * (C * ‖(x + t • v) - x‖)) * ‖g x‖ := by
        gcongr; exact LipschitzWith.norm_sub_le hf (x + t • v) x
      _ = (C * ‖v‖) *‖g x‖ := by field_simp [norm_smul, abs_of_nonneg t_pos.le]; ring
      _ = K.indicator (fun x ↦ (C * ‖v‖) * ‖g x‖) x := by rw [indicator_of_mem hx]
    · have A : f x = 0 := by
        rw [← Function.nmem_support]
        contrapose! hx
        exact self_subset_cthickening _ (subset_tsupport _ hx)
      have B : f (x + t • v) = 0 := by
        rw [← Function.nmem_support]
        contrapose! hx
        apply mem_cthickening_of_dist_le _ _  (‖v‖) (tsupport f) (subset_tsupport _ hx)
        simp only [dist_eq_norm, sub_add_cancel', norm_neg, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg t_pos.le, norm_pos_iff]
        exact mul_le_of_le_one_left (norm_nonneg v) ht.2
      simp only [B, A, _root_.sub_self, smul_eq_mul, mul_zero, zero_mul, norm_zero]
      exact indicator_nonneg (fun y _hy ↦ by positivity) _
  · rw [integrable_indicator_iff K_compact.measurableSet]
    apply ContinuousOn.integrableOn_compact K_compact
    exact (Continuous.mul continuous_const hg.norm).continuousOn
  · filter_upwards [hf.ae_lineDifferentiableAt v] with x hx
    exact hx.hasLineDerivAt.tendsto_nhdsWithin_right.mul tendsto_const_nhds

/-- Integration by parts formula for the line derivative of Lipschitz functions, assuming one of
them is compactly supported. -/
theorem integral_lineDeriv_mul_eq
    (hf : LipschitzWith C f) (hg : LipschitzWith D g) (h'g : HasCompactSupport g) (v : E) :
    ∫ x, lineDeriv ℝ f x v * g x ∂μ = ∫ x, lineDeriv ℝ g x (-v) * f x ∂μ := by
  /- Write down the line derivative as the limit of `(f (x + t v) - f x) / t` and
  `(g (x - t v) - g x) / t`, and therefore the integrals as limits of the corresponding integrals
  thanks to the dominated convergence theorem. At fixed positive `t`, the integrals coincide
  (with the change of variables `y = x + t v`), so the limits also coincide. -/
  have A : Tendsto (fun (t : ℝ) ↦ ∫ x, (t⁻¹ • (f (x + t • v) - f x)) * g x ∂μ) (𝓝[>] 0)
              (𝓝 (∫ x, lineDeriv ℝ f x v * g x ∂μ)) :=
    integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul
      hf (hg.continuous.integrable_of_hasCompactSupport h'g) v
  have B : Tendsto (fun (t : ℝ) ↦ ∫ x, (t⁻¹ • (g (x + t • (-v)) - g x)) * f x ∂μ) (𝓝[>] 0)
              (𝓝 (∫ x, lineDeriv ℝ g x (-v) * f x ∂μ)) :=
    integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul' hg h'g hf.continuous (-v)
  suffices S1 : ∀ (t : ℝ), ∫ x, (t⁻¹ • (f (x + t • v) - f x)) * g x ∂μ =
                            ∫ x, (t⁻¹ • (g (x + t • (-v)) - g x)) * f x ∂μ by
    simp only [S1] at A; exact tendsto_nhds_unique A B
  intro t
  suffices S2 : ∫ x, (f (x + t • v) - f x) * g x ∂μ = ∫ x, f x * (g (x + t • (-v)) - g x) ∂μ by
    simp only [smul_eq_mul, mul_assoc, integral_mul_left, S2, mul_neg, mul_comm (f _)]
  have S3 : ∫ x, f (x + t • v) * g x ∂μ = ∫ x, f x * g (x + t • (-v)) ∂μ := by
    rw [← integral_add_right_eq_self _ (t • (-v))]; simp
  simp_rw [_root_.sub_mul, _root_.mul_sub]
  rw [integral_sub, integral_sub, S3]
  · apply Continuous.integrable_of_hasCompactSupport
    · exact hf.continuous.mul (hg.continuous.comp (continuous_add_right _))
    · exact (h'g.comp_homeomorph (Homeomorph.addRight (t • (-v)))).mul_left
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport h'g.mul_left
  · apply Continuous.integrable_of_hasCompactSupport
    · exact (hf.continuous.comp (continuous_add_right _)).mul hg.continuous
    · exact h'g.mul_left
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport h'g.mul_left

/-- The line derivative of a Lipschitz function is almost everywhere linear with respect to fixed
coefficients. -/
theorem ae_lineDeriv_sum_eq
    {ι : Type*} {s : Finset ι} {a : ι → ℝ} {v : ι → E} (hf : LipschitzWith C f) :
    ∀ᵐ x ∂μ, lineDeriv ℝ f x (∑ i in s, a i • v i) = ∑ i in s, a i • lineDeriv ℝ f x (v i) := by
  /- Clever argument by Morrey: integrate against a smooth compactly supported function `g`, switch
  the derivative to `g` by integration by parts, and use the linearity of the derivative of `g` to
  conclude that the initial integrals coincide. -/
  apply ae_eq_of_integral_contDiff_smul_eq (hf.locallyIntegrable_lineDeriv _)
    (locallyIntegrable_finset_sum _ (fun i hi ↦  (hf.locallyIntegrable_lineDeriv (v i)).smul (a i)))
    (fun g g_smooth g_comp ↦ ?_)
  simp_rw [Finset.smul_sum]
  have A : ∀ i ∈ s, Integrable (fun x ↦ g x • (a i • fun x ↦ lineDeriv ℝ f x (v i)) x) μ :=
    fun i hi ↦ (g_smooth.continuous.integrable_of_hasCompactSupport g_comp).smul_of_top_left
      ((hf.memℒp_lineDeriv (v i)).const_smul (a i))
  rw [integral_finset_sum _ A]
  suffices S1 : ∫ x, lineDeriv ℝ f x (∑ i in s, a i • v i) * g x ∂μ
      = ∑ i in s, a i * ∫ x, lineDeriv ℝ f x (v i) * g x ∂μ by
    dsimp only [smul_eq_mul, Pi.smul_apply]
    simp_rw [← mul_assoc, mul_comm _ (a _), mul_assoc, integral_mul_left, mul_comm (g _), S1]
  suffices S2 : ∫ x, (∑ i in s, a i * fderiv ℝ g x (v i)) * f x ∂μ =
                  ∑ i in s, a i * ∫ x, fderiv ℝ g x (v i) * f x ∂μ by
    obtain ⟨D, g_lip⟩ : ∃ D, LipschitzWith D g :=
      ContDiff.lipschitzWith_of_hasCompactSupport g_comp g_smooth le_top
    simp_rw [integral_lineDeriv_mul_eq hf g_lip g_comp]
    simp_rw [(g_smooth.differentiable le_top).differentiableAt.lineDeriv_eq_fderiv]
    simp only [map_neg, ContinuousLinearMap.map_sum, SMulHomClass.map_smul, smul_eq_mul, neg_mul]
    simp only [integral_neg, mul_neg, Finset.sum_neg_distrib, neg_inj]
    exact S2
  suffices B : ∀ i ∈ s, Integrable (fun x ↦ a i * (fderiv ℝ g x (v i) * f x)) μ by
    simp_rw [Finset.sum_mul, mul_assoc, integral_finset_sum s B, integral_mul_left]
  intro i _hi
  let L : (E →L[ℝ] ℝ) → ℝ := fun f ↦ f (v i)
  change Integrable (fun x ↦ a i * ((L ∘ (fderiv ℝ g)) x * f x)) μ
  refine (Continuous.integrable_of_hasCompactSupport ?_ ?_).const_mul _
  · exact ((g_smooth.continuous_fderiv le_top).clm_apply continuous_const).mul hf.continuous
  · exact ((g_comp.fderiv ℝ).comp_left rfl).mul_right

/-!
### Step 3: construct the derivative using the line derivatives along a basis
-/

theorem ae_exists_fderiv_of_countable
    (hf : LipschitzWith C f) {s : Set E} (hs : s.Countable) :
    ∀ᵐ x ∂μ, ∃ (L : E →L[ℝ] ℝ), ∀ v ∈ s, HasLineDerivAt ℝ f (L v) x v := by
  sorry

/-- If a Lipschitz functions has line derivatives in a dense set of directions which are given by
a single continuous linear map `L`, then it admits `L` as Fréchet derivative. -/
theorem hasFderivAt_of_hasLineDerivAt_of_closure {f : E → F}
    (hf : LipschitzWith C f) {s : Set E} (hs : sphere 0 1 ⊆ closure s)
    {L : E →L[ℝ] F} {x : E} (hL : ∀ v ∈ s, HasLineDerivAt ℝ f (L v) x v) :
    HasFDerivAt f L x :=
  sorry

theorem ae_differentiableAt_of_real (hf : LipschitzWith C f) :
    ∀ᵐ x ∂μ, DifferentiableAt ℝ f x := by
  obtain ⟨s, s_count, s_dense⟩ : ∃ (s : Set E), s.Countable ∧ Dense s :=
    TopologicalSpace.exists_countable_dense E
  have hs : sphere 0 1 ⊆ closure s := by rw [s_dense.closure_eq]; exact subset_univ _
  filter_upwards [hf.ae_exists_fderiv_of_countable s_count]
  rintro x ⟨L, hL⟩
  exact (hf.hasFderivAt_of_hasLineDerivAt_of_closure hs hL).differentiableAt

end LipschitzWith

variable [FiniteDimensional ℝ F]

namespace LipschitzOnWith

/-- A real-valued function on a finite-dimensional space which is Lipschitz on a set is
differentiable almost everywere in this set. Superseded by
`LipschitzOnWith.ae_differentiableWithinAt_of_mem` which works for functions taking value in any
finite-dimensional space. -/
theorem ae_differentiableWithinAt_of_mem_of_real (hf : LipschitzOnWith C f s) :
    ∀ᵐ x ∂μ, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  obtain ⟨g, g_lip, hg⟩ : ∃ (g : E → ℝ), LipschitzWith C g ∧ EqOn f g s := hf.extend_real
  filter_upwards [g_lip.ae_differentiableAt_of_real] with x hx xs
  exact hx.differentiableWithinAt.congr hg (hg xs)

/-- A function on a finite-dimensional space which is Lipschitz on a set and taking values in a
product space is differentiable almost everywere in this set. Superseded by
`LipschitzOnWith.ae_differentiableWithinAt_of_mem` which works for functions taking value in any
finite-dimensional space. -/
theorem ae_differentiableWithinAt_of_mem_pi_of_real
    {ι : Type*} [Fintype ι] {f : E → ι → ℝ} {s : Set E}
    (hf : LipschitzOnWith C f s) : ∀ᵐ x ∂μ, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  have A : ∀ i : ι, LipschitzWith 1 fun x : ι → ℝ => x i := fun i => LipschitzWith.eval i
  have : ∀ i : ι, ∀ᵐ x ∂μ, x ∈ s → DifferentiableWithinAt ℝ (fun x : E => f x i) s x := fun i ↦ by
    apply ae_differentiableWithinAt_of_mem_of_real
    exact LipschitzWith.comp_lipschitzOnWith (A i) hf
  filter_upwards [ae_all_iff.2 this] with x hx xs
  exact differentiableWithinAt_pi.2 fun i => hx i xs

/-- *Rademacher's theorem*: a function between finite-dimensional real vector spaces which is
Lipschitz on a set is differentiable almost everywere in this set. -/
theorem ae_differentiableWithinAt_of_mem {f : E → F} (hf : LipschitzOnWith C f s) :
    ∀ᵐ x ∂μ, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  let A := (Basis.ofVectorSpace ℝ F).equivFun.toContinuousLinearEquiv
  suffices H : ∀ᵐ x ∂μ, x ∈ s → DifferentiableWithinAt ℝ (A ∘ f) s x by
    filter_upwards [H] with x hx xs
    have : f = (A.symm ∘ A) ∘ f := by
      simp only [ContinuousLinearEquiv.symm_comp_self, Function.comp.left_id]
    rw [this]
    exact A.symm.differentiableAt.comp_differentiableWithinAt x (hx xs)
  apply ae_differentiableWithinAt_of_mem_pi_of_real
  exact A.lipschitz.comp_lipschitzOnWith hf

/-- *Rademacher's theorem*: a function between finite-dimensional real vector spaces which is
Lipschitz on a set is differentiable almost everywere in this set. -/
theorem ae_differentiableWithinAt {f : E → F} (hf : LipschitzOnWith C f s)
    (hs : MeasurableSet s) :
    ∀ᵐ x ∂(μ.restrict s), DifferentiableWithinAt ℝ f s x := by
  rw [ae_restrict_iff' hs]
  exact hf.ae_differentiableWithinAt_of_mem

end LipschitzOnWith

/-- *Rademacher's theorem*: a Lipschiz function between finite-dimensional real vector spaces is
differentiable almost everywhere. -/
theorem LipschitzWith.ae_differentiableAt {f : E → F} (h : LipschitzWith C f) :
    ∀ᵐ x ∂μ, DifferentiableAt ℝ f x := by
  rw [← lipschitzOn_univ] at h
  simpa [differentiableWithinAt_univ] using h.ae_differentiableWithinAt_of_mem
