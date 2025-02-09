
import Mathlib.Tactic


example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U) := by
  exact continuous_def

example (X Y : Type) [MetricSpace X] [MetricSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ x : X, ∀ ε > 0, ∃ δ > 0, ∀ x' : X, dist x' x < δ → dist (f x') (f x) < ε := by
  exact Metric.continuous_iff

example (X Y Z : Type) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z) (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
  rw [continuous_def] at *
  intro U hU
  rw [Set.preimage_comp]
  specialize hg U hU
  specialize hf (g ⁻¹' U) hg
  exact hf

example (X Y Z : Type) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z) (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
  continuity

example (X Y Z : Type) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z) (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
  exact Continuous.comp hg hf
