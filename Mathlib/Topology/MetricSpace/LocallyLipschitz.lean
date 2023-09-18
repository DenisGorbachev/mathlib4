import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.Topology.MetricSpace.Lipschitz
-- FIXME: move into a new section in Lipschitz.lean

import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
## Locally Lipschitz functions
Define locally Lipschitz functions and show their elementary properties.
Show that C¹ functions are locally Lipschitz.
-/

open Set Topology
set_option autoImplicit false

namespace LocallyLipschitz
variable {X Y Z: Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]

-- f : X → Y is locally Lipschitz iff every point `p ∈ X` has a neighourhood on which `f` is Lipschitz.
def LocallyLipschitz (f : X → Y) : Prop :=
  ∀ x : X, ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K f t

/-- A Lipschitz function is locally Lipschitz. -/
protected lemma of_Lipschitz {f : X → Y} (hf : ∃ K, LipschitzWith K f) :
    LocallyLipschitz f := by
  intro x
  obtain ⟨K, hK⟩ := hf
  use K, univ
  rw [lipschitzOn_univ]
  exact ⟨Filter.univ_mem, hK⟩

/-- The identity function is locally Lipschitz. -/
protected lemma id : LocallyLipschitz (@id X) := by
  apply LocallyLipschitz.of_Lipschitz
  use 1
  exact LipschitzWith.id

/-- Constant functions are locally Lipschitz. -/
protected lemma const (b : Y) : LocallyLipschitz (fun _ : X ↦ b) := by
  apply LocallyLipschitz.of_Lipschitz
  use 0
  exact LipschitzWith.const b

/-- C¹ functions are locally Lipschitz. -/
protected lemma of_C1 {E F: Type*} {f : E → E} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (hf : ContDiff ℝ 1 f) : LocallyLipschitz f := by
  intro x
  rcases (ContDiffAt.exists_lipschitzOnWith (ContDiff.contDiffAt hf)) with ⟨K, t, ht, hf⟩
  use K, t

open NNReal Set
-- tweaked version of the result in mathlib, weaker hypotheses -- not just restricting the domain,
-- but also weakening the assumption on the codomain
theorem comp_lipschitzOnWith' {Kf Kg : ℝ≥0} {f : Y → Z} {g : X → Y} {s : Set X}
    (hf : LipschitzOnWith Kf f (g '' s)) (hg : LipschitzOnWith Kg g s) : LipschitzOnWith (Kf * Kg) (f ∘ g) s := by
  intro x hx y hy
  calc edist ((f ∘ g) x) ((f ∘ g) y)
    _ ≤ Kf * edist (g x) (g y) := hf (mem_image_of_mem g hx) (mem_image_of_mem g hy)
    _ ≤ Kf * (Kg * edist x y) := by exact mul_le_mul_left' (hg hx hy) Kf
    _ = ↑(Kf * Kg) * edist x y := by rw [← mul_assoc, @ENNReal.coe_mul]

/-- The composition of locally Lipschitz functions is locally Lipschitz. --/
lemma LocallyLipschitz_comp {f : Y → Z} {g : X → Y}
    (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) : LocallyLipschitz (f ∘ g) := by
  intro x
  rcases hg x with ⟨Kg, t₁, ht₁, hgL⟩
  -- g is Lipschitz on t, f is Lipschitz on u ∋ g(x)
  rcases hf (g x) with ⟨Kf, u, hu, hfL⟩
  -- Consider the restriction of g to t. In particular, this restriction is Lipschitz and continuous.
  let f' := Set.restrict t₁ g
  -- have : LipschitzWith Kg f' := LipschitzOnWith.to_restrict hgL
  have : Continuous f' := LipschitzWith.continuous (LipschitzOnWith.to_restrict hgL)
  -- Thus, t₂ := g' ⁻¹ (u) is a neighbourhood of x in s and f is Lipschitz on g(t₂).
  let t₂ := f' ⁻¹' u
  let t₂ : Set X := t₂
  have : t₂ ∈ 𝓝 x := by sorry
  have h₁ : LipschitzOnWith Kg g t₂ := by
    refine LipschitzOnWith.mono hgL ?_
    sorry -- mathematically obvious
    --have : (f' ⁻¹' univ) : Set X ⊆ t₁ := by sorry --apply?
    --apply Set.subset_preimage_univ
  have h₂ : LipschitzOnWith Kf f (g '' t₂) := sorry
  -- apply comp_lipschitzOnWith' h₁ h₂
  sorry

-- /-- The sum of locally Lipschitz functions is locally Lipschitz. -/
-- lemma LocallyLipschitz_sum {f g : X → Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
--     (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) : LocallyLipschitz (f + g) := by
--   intro x
--   rcases hf x with ⟨Kf, t₁, h₁t, hfL⟩
--   rcases hg x with ⟨Kg, t₂, h₂t, hgL⟩
--   use Kf + Kg, t₁ ∩ t₂
--   have as: LipschitzOnWith Kf f (t₁∩t₂) := LipschitzOnWith.mono hfL (Set.inter_subset_left t₁ t₂)
--   have bs: LipschitzOnWith Kg g (t₁∩t₂) := LipschitzOnWith.mono hgL (Set.inter_subset_right t₁ t₂)
--   constructor
--   · exact Filter.inter_mem h₁t h₂t
--   · sorry -- exact?

section missing -- analogues of theorems for LipschitzWith
variable {α : Type*} [PseudoEMetricSpace α] {f g : α → ℝ} {Kf Kg : NNReal} {s : Set α}

protected theorem max (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg g s) :
    LipschitzOnWith (max Kf Kg) (fun x => max (f x) (g x)) s := by
  sorry --simpa only [(· ∘ ·), one_mul] using lipschitzWith_max.comp (hf.prod hg)

protected theorem min (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg g s) :
    LipschitzOnWith (max Kf Kg) (fun x => min (f x) (g x)) s := by
  sorry--simpa only [(· ∘ ·), one_mul] using lipschitzWith_min.comp (hf.prod hg)

theorem max_const (hf : LipschitzOnWith Kf f s) (a : ℝ) :
    LipschitzOnWith Kf (fun x => max (f x) a) s := by
  sorry --simpa only [max_eq_left (zero_le Kf)] using hf.max (LipschitzWith.const a)

theorem const_max (hf : LipschitzOnWith Kf f s) (a : ℝ) : LipschitzOnWith Kf (fun x => max a (f x)) s := by
  simpa only [max_comm] using hf.max_const a

theorem min_const (hf : LipschitzOnWith Kf f s) (a : ℝ) : LipschitzOnWith Kf (fun x => min (f x) a) s := by
  sorry --simpa only [max_eq_left (zero_le Kf)] using hf.min (LipschitzWith.const a)

theorem const_min (hf : LipschitzOnWith Kf f s) (a : ℝ) : LipschitzOnWith Kf (fun x => min a (f x)) s := by
  simpa only [min_comm] using hf.min_const a
end missing


/-- The minimum of locally Lipschitz functions is locally Lipschitz. -/
lemma LocallyLipschitz_min {f g : X → ℝ} (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x => min (f x) (g x)) := by
  intro x
  rcases hf x with ⟨Kf, t₁, h₁t, hfL⟩
  rcases hg x with ⟨Kg, t₂, h₂t, hgL⟩
  use max Kf Kg, t₁ ∩ t₂
  have hfL' : LipschitzOnWith Kf f (t₁∩t₂) := LipschitzOnWith.mono hfL (inter_subset_left t₁ t₂)
  have hgL' : LipschitzOnWith Kg g (t₁∩t₂) := LipschitzOnWith.mono hgL (inter_subset_right t₁ t₂)
  exact ⟨Filter.inter_mem h₁t h₂t, LipschitzOnWith.min hfL' hgL'⟩

/-- The maximum of locally Lipschitz functions is locally Lipschitz. -/
lemma LocallyLipschitz_max {f g : X → ℝ} (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x => max (f x) (g x)) := by
  intro x
  rcases hf x with ⟨Kf, t₁, h₁t, hfL⟩
  rcases hg x with ⟨Kg, t₂, h₂t, hgL⟩
  use max Kf Kg, t₁ ∩ t₂
  have hfL' : LipschitzOnWith Kf f (t₁∩t₂) := LipschitzOnWith.mono hfL (inter_subset_left t₁ t₂)
  have hgL' : LipschitzOnWith Kg g (t₁∩t₂) := LipschitzOnWith.mono hgL (inter_subset_right t₁ t₂)
  exact ⟨Filter.inter_mem h₁t h₂t, LipschitzOnWith.max hfL' hgL'⟩

-- /-- Multiplying a locally Lipschitz function by a constant remains locally Lipschitz. -/
-- lemma LocallyLipschitz_scalarProduct {f : X → Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (hf : LocallyLipschitz f) {a : ℝ} :
--     LocallyLipschitz (fun x ↦ a • f x) := by
--   intro x
--   rcases hf x with ⟨Kf, t, ht, hfL⟩
--   use 42 -- (abs(a) * Kf)
--   use t
--   constructor
--   · exact ht
--   · done

-- /-- The function x → x² is locally Lipschitz, but not Lipschitz. -/
-- example : LocallyLipschitz (fun x : ℝ  ↦ x^2) ∧ ¬ ∃ K, LipschitzWith K (fun x : ℝ ↦ x^2) := by
--   have : ContDiff ℝ 1 (fun x : ℝ ↦ x^2) := by sorry
--   constructor
--   · apply LocallyLipschitz.of_C1 this (E := ℝ) (F := ℝ)
--   · rintro ⟨K, hf⟩
--     -- choose x ∈ R s.t. 2x+1>K, for instance x=K will do this
--     have : K < 2 * K + 1 := by sorry
--     let f : ℝ → ℝ := fun x ↦ x^2
--     have : f (K + 1) - f K = 2 * K + 1 := by ring
end LocallyLipschitz
