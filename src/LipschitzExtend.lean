/-
Copyright (c) 2023 Chris Camaño, Ian Bunner
Authors: Chris Camaño, Ian Bunner
-/
import Mathlib.Topology.MetricSpace.Lipschitz 
import Mathlib.Analysis.NormedSpace.lpSpace
import Mathlib.Data.Real.ENNReal
import Mathlib.Data.Set.Function
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.Group.Defs

open  ENNReal Metric Function Set Function
open scoped NNReal BigOperators Group

@[app_unexpander abs] def unexpandAbs : Lean.PrettyPrinter.Unexpander
  | `($(_) $x) => `(|$x|)
  | _ => throw ()

/- A function `f : α → (ι → ℝ)` which is `K`-Lipschitz on a subset `s` admits a `K`-Lipschitz
extension to the whole space. -/

local notation "ℓ^∞(" ι ")" => lp (fun i : ι => ℝ) ∞

variable {α β : Type _}
lemma LipschitzWith.uniformly_bounded [PseudoMetricSpace α] (g : α → ι → ℝ) {K : ℝ≥0}
    (hg : ∀ i, LipschitzWith K (g · i)) (a₀ : α) (hga₀b : Memℓp (g a₀) ∞) (a : α) :
    Memℓp (g a) ∞ := by
  rcases hga₀b with ⟨M, hM⟩
  use ↑K * dist a a₀ + M
  rintro - ⟨i, rfl⟩
  calc
    |g a i| = |g a i - g a₀ i + g a₀ i| := by simp
    _ ≤ |g a i - g a₀ i| + |g a₀ i| := abs_add _ _
    _ ≤ ↑K * dist a a₀ + M := by
        gcongr
        . exact lipschitzWith_iff_dist_le_mul.1 (hg i) a a₀
        . exact hM ⟨i, rfl⟩

theorem LipschitzOnWith.coordinate [PseudoMetricSpace α] (f : α → ℓ^∞(ι)) (s : Set α) (K : ℝ≥0) :
    LipschitzOnWith K f s ↔ ∀ i : ι, LipschitzOnWith K (fun a : α ↦ f a i) s := by
  simp_rw [lipschitzOnWith_iff_dist_le_mul]
  constructor
  · intro hfl i x hx y hy
    calc
      dist (f x i) (f y i) ≤ dist (f x) (f y) := lp.norm_apply_le_norm top_ne_zero (f x - f y) i
      _ ≤ K * dist x y := hfl x hx y hy
  · intro hgl x hx y hy
    apply lp.norm_le_of_forall_le; positivity
    intro i
    apply hgl i x hx y hy

theorem LipschitzWith.coordinate [PseudoMetricSpace α] {f : α → ℓ^∞(ι)} (K : ℝ≥0) :
    LipschitzWith K f ↔ ∀ i : ι, LipschitzWith K (fun a : α ↦ f a i) := by
  simp_rw [← lipschitz_on_univ]
  apply LipschitzOnWith.coordinate

theorem const'[PseudoMetricSpace α] [PseudoMetricSpace β] (b : β) {K : ℝ≥0} : LipschitzWith K fun _ : α => b := fun x y => by
  simp only [edist_self, zero_le]

/--
A function `f : α → ℓ^∞(ι, ℝ)` which is `K`-Lipschitz on a subset `s` admits a `K`-Lipschitz
extension to the whole space.

Theorem 2.2 of [Assaf Naor, *Metric Embeddings and Lipschitz Extensions*][Naor-2015]

The same result for the case of a finite type `ι` is implemented in
`LipschitzOnWith.extend_pi`.
-/
theorem LipschitzOnWith.extend_lp_infty [PseudoMetricSpace α] {s : Set α} {f : α → ℓ^∞(ι)}
    {K : ℝ≥0} (hfl : LipschitzOnWith K f s): ∃ g : α → ℓ^∞(ι), LipschitzWith K g ∧ EqOn f g s := by
  -- Construct the coordinate-wise extensions
  have : ∀ i : ι, ∃ g : α → ℝ, LipschitzWith K g ∧ EqOn (fun x => f x i) g s
  · intro i
    apply LipschitzOnWith.extend_real -- use the nonlinear Hahn-Banach theorem here!
    revert i
    rw [← LipschitzOnWith.coordinate]
    exact hfl
  choose g hgl hgeq using this
  rcases s.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀_in_s⟩
  . exact ⟨fun _ ↦ 0, const' 0, by simp⟩
  · -- Show that the extensions are uniformly bounded
    have hf_extb : ∀ a : α, Memℓp (swap g a) ∞
    . apply LipschitzWith.uniformly_bounded (swap g) hgl a₀
      use ‖f a₀‖
      rintro - ⟨i, rfl⟩
      simp_rw [←hgeq i ha₀_in_s]
      exact lp.norm_apply_le_norm top_ne_zero (f a₀) i
    -- Construct witness by bundling the function with its certificate of membership in ℓ^∞
    let f_ext' : α → ℓ^∞(ι) := fun i ↦ ⟨swap g i, hf_extb i⟩
    refine ⟨f_ext', ?_, ?_⟩
    · rw [LipschitzWith.coordinate]
      exact hgl
    · intro a hyp
      ext i
      exact (hgeq i) hyp
