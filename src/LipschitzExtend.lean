import Mathlib.Topology.MetricSpace.Lipschitz 
import Mathlib.Analysis.NormedSpace.lpSpace
import Mathlib.Data.Real.ENNReal
import Mathlib.Data.Set.Function

open ENNReal NNReal Metric Function Set 

/-- A function `f : α → (ι → ℝ)` which is `K`-Lipschitz on a subset `s` admits a `K`-Lipschitz
extension to the whole space.
TODO: state the same result (with the same proof) for the space `ℓ^∞ (ι, ℝ)` over a possibly
infinite type `ι`. -/

/-`ℓ²(ι, 𝕜)` is the Hilbert space of square-summable functions `ι → 𝕜`, herein implemented
as `lp (fun i : ι => 𝕜) 2`. -/

/-
Observations: 
the fucntional f is actually defined for the whole space in this proof, we instead impose Lipschitz
properties only on the subspace s and hope to extend this property to all of α
-/

notation "ℓ^∞(" ι ") " => lp (fun i : ι => ℝ ) ∞


theorem LipschitzOnWith.extend_pi' 
  [PseudoMetricSpace α]         -- α is a metric space 
  {s : Set α}                   -- s is a subspace of α
  {f : α → ℓ^∞(ι)}              -- f is a function from α to l_∞ of index set iota for components 
  {K : ℝ≥0}                     -- K is a non negative scalar for the lipshitz condition
  
  (hfl : LipschitzOnWith K f s) : -- hyp:the function is lipschitz on s with scalar K 
  
  ∃ g : α → ℓ^∞(ι), LipschitzWith K g ∧ EqOn f g s := by
  have : ∀ i : ι, ∃ g : α → ℝ, LipschitzWith K g ∧ EqOn (fun x => f x i) g s := fun i => by
    have : LipschitzOnWith K (fun x : α => f x i) s := by
      refine @LipschitzOnWith.of_dist_le_mul α ℝ _ _ K s (fun x => f x i) ?_
      dsimp
      intro x hx y hy
      rw [dist_eq_norm]
      -- dsimp
      calc ‖f x i - f y i‖ ≤ ‖f x - f y‖ := sorry
        _ ≤ K * dist x y := sorry
      -- fun x hx y hy =>by 
      -- dist_eq_norm
        
      
      -- (dist_le_pi_dist _ _ i).trans (hf.dist_le_mul x hx y hy)
    exact this.extend_real

  choose g hg using this

  refine' ⟨fun x i => g i x, LipschitzWith.of_dist_le_mul fun x y => _, _⟩
  · exact (dist_pi_le_iff (mul_nonneg K.2 dist_nonneg)).2 fun i => (hg i).1.dist_le_mul x y
  · intro x hx
    ext1 i
    exact (hg i).2 hx

#align lipschitz_on_with'.extend_pi LipschitzOnWith.extend_pi


/- [Original implementation] finite 
/-- A function `f : α → (ι → ℝ)` which is `K`-Lipschitz on a subset `s` admits a `K`-Lipschitz
extension to the whole space.
TODO: state the same result (with the same proof) for the space `ℓ^∞ (ι, ℝ)` over a possibly
infinite type `ι`. -/

theorem LipschitzOnWith.extend_pi
 [PseudoMetricSpace α] \
 [Fintype ι]
  {f : α → ι → ℝ} 
  {s : Set α}
  {K : ℝ≥0}
  (hf : LipschitzOnWith K f s) : 
  ∃ g : α → ι → ℝ, LipschitzWith K g ∧ EqOn f g s := by
  have : ∀ i, ∃ g : α → ℝ, LipschitzWith K g ∧ EqOn (fun x => f x i) g s := fun i => by
    have : LipschitzOnWith K (fun x : α => f x i) s :=
      LipschitzOnWith.of_dist_le_mul fun x hx y hy =>
        (dist_le_pi_dist _ _ i).trans (hf.dist_le_mul x hx y hy)
    exact this.extend_real
  choose g hg using this
  refine' ⟨fun x i => g i x, LipschitzWith.of_dist_le_mul fun x y => _, _⟩
  · exact (dist_pi_le_iff (mul_nonneg K.2 dist_nonneg)).2 fun i => (hg i).1.dist_le_mul x y
  · intro x hx
    ext1 i
    exact (hg i).2 hx
#align lipschitz_on_with.extend_pi LipschitzOnWith.extend_pi
-/