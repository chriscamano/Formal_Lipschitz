import Mathlib.Topology.MetricSpace.Lipschitz 
import Mathlib.Analysis.NormedSpace.lpSpace
import Mathlib.Data.Real.ENNReal
import Mathlib.Data.Set.Function

open  ENNReal Metric Function Set
open scoped NNReal BigOperators

/- A function `f : α → (ι → ℝ)` which is `K`-Lipschitz on a subset `s` admits a `K`-Lipschitz
extension to the whole space.
TODO: state the same result (with the same proof) for the space `ℓ^∞ (ι, ℝ)` over a possibly
infinite type `ι`. -/

/- `ℓ²(ι, 𝕜)` is the Hilbert space of square-summable functions `ι → 𝕜`, herein implemented
as `lp (fun i : ι => 𝕜) 2`. -/

notation "ℓ^∞(" ι ") " => lp (fun i : ι => ℝ ) ∞

variable {α : Type _} --{E : α → Type _} {p q : ℝ≥0∞} --[∀ i, NormedAddCommGroup (E i)]

theorem LipschitzOnWith.extend_linf [PseudoMetricSpace α] {s : Set α} {f : α → ℓ^∞(ι)} 
{K : ℝ≥0} (hfl : LipschitzOnWith K f s): ∃ g : α → ℓ^∞(ι), LipschitzWith K g ∧ EqOn f g s := by
  let E : ι → Type _ := (fun i : ι ↦ ℝ)
  have : ∀ i : ι, ∃ g : α → ℝ, LipschitzWith K g ∧ EqOn (fun x => f x i) g s := fun i => by
    have : LipschitzOnWith K (fun x : α => f x i) s
    · rw [lipschitzOnWith_iff_dist_le_mul] 
      rw [lipschitzOnWith_iff_dist_le_mul] at hfl
      intro x hx y hy
      have := @lp.norm_apply_le_norm
      calc 
        dist (f x i) (f y i) ≤ dist (f x) (f y) := lp.norm_apply_le_norm top_ne_zero (f x - f y ) i
        _ ≤ K * dist x y :=  hfl x hx y hy
    exact this.extend_real
  choose g hg using this
  rcases s.eq_empty_or_nonempty with rfl| ⟨a₀, ha₀_in_s⟩
  · sorry
  · let f_ext : α → ι → ℝ := fun x i => g i x
    have hf_extb : ∀ a : α, Memℓp (f_ext a) ∞ :=by 
      intro a
      rw [memℓp_infty_iff]
      have M:ℝ := sorry
      use K * dist a a₀ + M
      rintro - ⟨i, rfl⟩
      dsimp
      calc
        abs (f_ext a) ≤  abs (f_ext a + f a₀ - f a₀)  := 
        _≤ abs (f_ext a - f a₀) + abs (f a₀) := 
        _≤ abs (f_ext a + f a₀) := 
        _≤



      -- use K
      -- rw[ mem_upperBounds]
      -- simp
      -- intro x
      -- specialize hg x
      -- unfold LipschitzWith at hg

  let f_ext' : α → ℓ^∞(ι) := fun i ↦ ⟨f_ext i, hf_extb i⟩
  use f_ext'
  dsimp
  sorry





  -- show LipschitzWith K f_ext ∧ EqOn f g s

  -- refine' ⟨fun x i => g i x, LipschitzWith.of_dist_le_mul fun x y => _, _⟩
  -- · exact (dist_pi_le_iff (mul_nonneg K.2 dist_nonneg)).2 fun i => (hg i).1.dist_le_mul x y
  -- · intro x hx
  --   ext1 i
  --   exact (hg i).2 hx


