open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Fin
open import Function

open import Logic.Logic

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.InitialAlgebra
open import IDesc.FinalCoalgebra


module IDesc.AdjointFold where

record AdjointScheme {I : Set}{X : I → Set}(F : func I I) : Set₁ where

  field
    L : func I I
    R : func I I
    η : ∀ {X} → X ⇒ ⟦ R ◎ L ⟧func X
    ε : ∀ {X} → ⟦ L ◎ R ⟧func X ⇒ X

  G : func I I
  G = L ◎ F ◎ R

  σ : ∀ {X} → ⟦ L ◎ F ⟧func X ⇒ ⟦ G ◎ L ⟧func X
  σ {X} {i = i} = ◎-assoc' {F = L ◎ F} {G = R} {H = L} ∘ ◎-⟦⟧-distrib' {F = L ◎ F} {G = R ◎ L} ∘ ⟦ L ◎ F ⟧fmap η

  G' : func I I
  G' = R ◎ F ◎ L

  τ : ∀ {X} → ⟦ G' ◎ R ⟧func X ⇒ ⟦ R ◎ F ⟧func X
  τ = ⟦ R ◎ F ⟧fmap ε ∘ ◎-⟦⟧-distrib'' {F = R ◎ F} {G = L ◎ R} ∘ ◎-assoc'' {F = R ◎ F} {G = L} {H = R}

  {-# NON_TERMINATING #-}
  ⊣-fold : (⟦ G ⟧func X ⇒ X) → ⟦ L ⟧func (μ F) ⇒ X
  ⊣-fold a = a ∘ ⟦ G ⟧fmap (⊣-fold a) ∘ ◎-⟦⟧-distrib'' {F = G} ∘ σ ∘ ◎-⟦⟧-distrib' {F = L} ∘ ⟦ L ⟧fmap (inᵒ F)

  {-# NON_TERMINATING #-}
  ⊣-unfold : (X ⇒ ⟦ G' ⟧func X) → X ⇒ ⟦ R ⟧func (ν F)
  ⊣-unfold c = ⟦ R ⟧fmap (outᵒ F) ∘ ◎-⟦⟧-distrib'' {F = R} ∘ τ ∘ ◎-⟦⟧-distrib' {F = G'} ∘ ⟦ G' ⟧fmap (⊣-unfold c) ∘ c

open AdjointScheme

IdId : ∀ {I X F} → AdjointScheme {I} {X} F
IdId = record { L = mk `var ; R = mk `var ; η = id ; ε = id }

cata : ∀ {I X F} → (⟦ G {I} {X} {F} IdId ⟧func X ⇒ X) → μ F ⇒ X
cata = ⊣-fold IdId

ana : ∀ {I X F} → (X ⇒ ⟦ G {I} {X} {F} IdId ⟧func X) → X ⇒ ν F
ana = ⊣-unfold IdId

×→ : ∀ {I X}(A : Set)(F : func I I) → AdjointScheme {I} {X} F
×→ A F = record { L = mk λ i → `Σ A λ _ → `var i
                ; R = mk λ i → `Π A λ _ → `var i
                ; η = flip _,_
                ; ε = uncurry (flip _$_)}

para : ∀ {A I X F} → (⟦ G {I} {X} {F} (×→ A F) ⟧func X ⇒ X) → ⟦ L {X = X} (×→ A F) ⟧func (μ F) ⇒ X
para {A} {F = F} = ⊣-fold (×→ A F)

+△ : ∀ {I X}(F : func I I) → AdjointScheme {I} {X} F
+△ F = record { L = mk λ i → `σ 2 λ { zero → `var i ; (suc zero) → `var i ; (suc (suc ())) }
              ; R = mk λ i → `var i `× `var i
              ; η = < (λ x → zero , x) , (λ x → (suc zero) , x) >
              ; ε = λ { (zero , xy) → proj₁ xy ; (suc zero , xy) → proj₂ xy ; (suc (suc ()) , _) } }

apo : ∀ {I X F} → (X ⇒ ⟦ G' {I} {X} {F} (+△ F) ⟧func X) → X ⇒ ⟦ R {X = X} (+△ F) ⟧func (ν F)
apo {F = F} = ⊣-unfold (+△ F)
