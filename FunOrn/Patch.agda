module FunOrn.Patch where



open import Data.Unit
open import Data.Product

open import Logic.Logic

open import IDesc.Fixpoint

open import Orn.Ornament
open import Orn.Reornament

open import FunOrn.Functions
open import FunOrn.FunOrnament

-- Paper: Definition 5.15
Patch : ∀{T : Type } → ⟦ T ⟧Type → FunctionOrn T → Set 
Patch {T = μ D [ ._ ]→ T} f (μ⁺ o [ inv i⁺ ]→ T⁺) = 
      (x : μ D _) → 
         μ ⌈ o ⌉D (i⁺ , x) → Patch (f x) T⁺
Patch {T = μ D [ ._ ]× T} (x , t) (μ⁺ o [ inv i⁺ ]× T⁺) =
      μ ⌈ o ⌉D (i⁺ , x) × Patch t T⁺
Patch {T = `⊤} tt `⊤ = ⊤

record ptch {I I⁺ : Set}{u : I⁺ → I}(T : type I)(fo : forn T u) : Set₁ where
  constructor mk
  field
    out : (i⁺ : I⁺) →  (f : ⟦ T ⟧type (u i⁺)) → Patch {type.out T (u i⁺)} f (forn.out fo i⁺)

⟦_⟧patch : ∀ {I I⁺ : Set}{u : I⁺ → I}{T : type I}{fo : forn T u} →
           ptch {I}{I⁺}{u} (mk (type.out T)) fo →
           ((i⁺ : I⁺) → (f : ⟦ T ⟧type (u i⁺)) → Patch {type.out T (u i⁺)} f (forn.out fo i⁺))
⟦ p ⟧patch i⁺ f = ptch.out p i⁺ f
