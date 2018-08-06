open import Data.Unit
open import Data.Product
open import Function

open import Logic.Logic

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.InitialAlgebra

module IDesc.AdjointFold where

record AdjointScheme {I : Set}{X : I → Set}(F : func I I) : Set₁ where

  field
    L : func I I
    R : func I I
    η : ∀ {X} → X ⇒ ⟦ R ⟧func (⟦ L ⟧func X)
    ε : ∀ {X} → ⟦ L ⟧func (⟦ R ⟧func X) ⇒ X

  G : (I → Set) → (I → Set)
  G x = ⟦ L ⟧func (⟦ F ⟧func (⟦ R ⟧func x))

  σ : ∀ {X} → ⟦ L ⟧func (⟦ F ⟧func X) ⇒ G (⟦ L ⟧func X)
  σ = ⟦ L ⟧fmap (⟦ F ⟧fmap η)

  G' : (I → Set) → (I → Set)
  G' x = ⟦ R ⟧func (⟦ F ⟧func (⟦ L ⟧func x))

  τ : ∀ {X} → G' (⟦ R ⟧func X) ⇒ ⟦ R ⟧func (⟦ F ⟧func X )
  τ = ⟦ R ⟧fmap (⟦ F ⟧fmap ε)

  {-# NON_TERMINATING #-}
  ⊣-fold : (G X ⇒ X) → ⟦ L ⟧func (μ F) ⇒ X
  ⊣-fold a = a ∘ ⟦ L ⟧fmap (⟦ F ⟧fmap (⟦ R ⟧fmap (⊣-fold a))) ∘ σ ∘ ⟦ L ⟧fmap (inᵒ F)

open AdjointScheme

×→ : ∀ {X}(A : Set)(F : func ⊤ ⊤)  → AdjointScheme {⊤} {X} F
×→ A F = record { L = mk λ _ → `Σ A λ _ → `var tt
                ; R = mk λ _ → `Π A λ _ → `var tt
                ; η = flip _,_
                ; ε = uncurry (flip _$_)}

para : ∀ {A F X} → (G {X = X} (×→ A F) X ⇒ X) → ⟦ L {X = X} (×→ A F) ⟧func (μ F) tt → X tt
para {A} {F} a = ⊣-fold (×→ A F) a
