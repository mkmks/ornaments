open import Data.Unit
open import Data.Product

open import Logic.Logic

open import IDesc.IDesc
open import IDesc.Fixpoint

module IDesc.InitialAlgebra
          {I : Set}
          (D : func I I) where

Alg : (I → Set) → Set
Alg X = ⟦ D ⟧func X ⇒ X

module Fold  {X : I → Set }(α : Alg X)
       where

  mutual
    fold : μ D ⇒ X
    fold ⟨ xs ⟩ = α (hyps (func.out D _) xs)

    hyps : (D' : IDesc  I) → 
           (xs : ⟦ D' ⟧ (μ D)) →
           ⟦ D' ⟧ X
    hyps `1 tt = tt
    hyps (`var i) xs = fold xs
    hyps (T `× T') (t , t') = hyps T t , hyps T' t'
    hyps (`σ n T) (k , xs) = k , hyps (T k) xs
    hyps (`Σ S T) (s , xs) = s , hyps (T s) xs
    hyps (`Π S T) f = λ s → hyps (T s) (f s)

-- Paper typesetting: (| _ |)
fold : {X : I → Set }(α : Alg X) → μ D ⇒ X
fold = Fold.fold

inᵒ : μ D ⇒ ⟦ D ⟧func (μ D)
inᵒ = fold (⟦ D ⟧fmap ⟨_⟩)
