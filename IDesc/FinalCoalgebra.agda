open import Data.Unit
open import Data.Product

open import Logic.Logic

open import IDesc.IDesc
open import IDesc.Fixpoint

module IDesc.FinalCoalgebra
          {I : Set}
          (D : func I I) where

Coalg : (I → Set) → Set
Coalg X = X ⇒ ⟦ D ⟧func X

open IDesc.Fixpoint.ν

module Unfold  {X : I → Set }(γ : Coalg X)
       where

    unfold : X ⇒ ν D
    hyps : (D' : IDesc  I) → ⟦ D' ⟧ X → ⟦ D' ⟧ (ν D)
           
    ⟩ unfold x ⟨ = hyps (func.out D _) (γ x)

    hyps (`var i) xs = unfold xs
    hyps `1 tt = tt
    hyps (`Σ S T) (s , xs) = s , hyps (T s) xs
    hyps (`Π S T) f = λ s → hyps (T s) (f s)
    hyps (T `× T') (t , t') = hyps T t , hyps T' t'
    hyps (`σ n T) (k , xs) = k , (hyps (T k) xs)

unfold : {X : I → Set }(γ : Coalg X) → X ⇒ ν D
unfold = Unfold.unfold

outᵒ : ⟦ D ⟧func (ν D) ⇒ ν D
outᵒ = unfold (⟦ D ⟧fmap ⟩_⟨)
