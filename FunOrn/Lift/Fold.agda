 

open import IDesc.IDesc

open import Orn.Ornament

module FunOrn.Lift.Fold 
         {I I⁺ : Set }
         {D : func  I I}
         {u : I⁺ → I}
         (o : orn D u u)
       where

open import Data.Product

open import Logic.Logic 

open import IDesc.InitialAlgebra

open import Orn.Reornament

open import FunOrn.Functions
open import FunOrn.FunOrnament
open import FunOrn.Patch

-- Paper: Definition 6.4
-- Typeset: lift_{Alg}
liftAlg : ∀{T : type I} → Alg D (λ i → ⟦ T ⟧type i) → forn T u → Set 
--liftAlg α T⁺ = Alg ⌈ o ⌉D (λ ix → Patch {i⁺ = inv (proj₁ ix)} (fold D α (proj₂ ix)) T⁺)
liftAlg α T⁺ = Alg ⌈ o ⌉D (λ ix → Patch (fold D α (proj₂ ix)) (forn.out T⁺ (proj₁ ix)))

-- Paper: Definition 6.5
lift-fold : {i⁺ : I⁺}--{i : I}{i⁺ : u ⁻¹ i}
          {T : type I}{T⁺ : forn T u}
          (α : Alg D (λ i → ⟦ T ⟧type i))
          (β : liftAlg α T⁺) →
--    Patch {I}{I⁺}{i}{u}{i⁺}{mk (λ x → μ D [ i ]→ type.out T x)}
    Patch {μ D [ u i⁺ ]→ type.out T (u i⁺)}
      (fold D α) (μ⁺ o [ inv i⁺ ]→ forn.out T⁺ i⁺)
lift-fold {i⁺} α β = 
  λ x x⁺⁺ → fold ⌈ o ⌉D (λ {ix} ih → β {ix} ih) x⁺⁺
