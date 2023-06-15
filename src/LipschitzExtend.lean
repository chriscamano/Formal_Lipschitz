import Mathlib.Topology.MetricSpace.Lipschitz 
import Mathlib.Analysis.NormedSpace.lpSpace
import Mathlib.Data.Real.ENNReal
import Mathlib.Data.Set.Function
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.Group.Defs

open  ENNReal Metric Function Set 
open scoped NNReal BigOperators Group

@[app_unexpander abs] def unexpandAbs : Lean.PrettyPrinter.Unexpander
  | `($(_) $x) => `(|$x|)
  | _ => throw ()

/- A function `f : α → (ι → ℝ)` which is `K`-Lipschitz on a subset `s` admits a `K`-Lipschitz
extension to the whole space. -/

notation "ℓ^∞(" ι ") " => lp (fun i : ι => ℝ ) ∞

variable {α β : Type _}

theorem lipschitzWith_const [PseudoMetricSpace α] [PseudoMetricSpace β] (b: β) (K : ℝ≥0):
  LipschitzWith K (fun _ : α ↦ b):= by
  intro x y; simp

theorem LipschitzOnWith.extend_linf [PseudoMetricSpace α] {s : Set α} {f : α → ℓ^∞(ι)} 
{K : ℝ≥0} (hfl : LipschitzOnWith K f s): ∃ g : α → ℓ^∞(ι), LipschitzWith K g ∧ EqOn f g s := by
  
  have : ∀ i : ι, ∃ g : α → ℝ, LipschitzWith K g ∧ EqOn (fun x => f x i) g s := fun i => by
    have : LipschitzOnWith K (fun x : α => f x i) s
    · rw [lipschitzOnWith_iff_dist_le_mul] at hfl ⊢
      intro x hx y hy
      calc 
        dist (f x i) (f y i) ≤ dist (f x) (f y) := lp.norm_apply_le_norm top_ne_zero (f x - f y ) i
        _ ≤ K * dist x y :=  hfl x hx y hy
    exact this.extend_real
  choose g hg using this
  rcases s.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀_in_s⟩
  . exact ⟨fun _ ↦ 0, lipschitzWith_const 0 K, by simp⟩
  · let f_ext : α → ι → ℝ := fun x i ↦ g i x --<-------- golf me?
    have hf_extb : ∀ a : α, Memℓp (f_ext a) ∞ := by 
      intro a
      let M : ℝ := ‖f a₀‖
      use K * dist a a₀ + M
      rintro - ⟨i, rfl⟩
      rcases hg i with ⟨hgl, hgr⟩
      calc
        |g i a| = abs (g i a - f a₀ i + f a₀ i) := by simp
        _ ≤ abs (g i a - f a₀ i) + abs (f a₀ i) :=  abs_add _ _ --<-------- golf me
        _ ≤ abs (g i a - g i a₀ ) + abs (g i a₀ - f a₀ i) + abs (f a₀ i) := by gcongr; apply abs_sub_le 
        _ = abs (g i a - g i a₀ ) + abs (f a₀ i) := by simp [hgr ha₀_in_s, sub_self _]
        _ ≤ ↑K * dist a a₀ + abs (f a₀ i):= by 
            gcongr
            exact lipschitzWith_iff_dist_le_mul.1 hgl a a₀
        _ ≤ ↑K * dist a a₀ + M := by
            gcongr
            exact lp.norm_apply_le_norm top_ne_zero (f a₀) i
    let f_ext' : α → ℓ^∞(ι) := fun i ↦ ⟨f_ext i, hf_extb i⟩
    refine ⟨f_ext', ?_, ?_⟩
    · rw [lipschitzWith_iff_dist_le_mul]
      intro x y 
      apply lp.norm_le_of_forall_le; positivity
      exact fun i ↦ lipschitzWith_iff_dist_le_mul.mp (hg i).1 x y
    · intro a hyp
      ext i --<-------- golf me
      exact (hg i).2 hyp 
