{-# OPTIONS --safe --without-K --prop --postfix-projections #-}

open import Algebra.Po
open import Level

module Generic.Linear.Extend
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open PoSemiring poSemiring renaming (Carrier to Ann; _≤_ to _⊴_)

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.Product
  open import Relation.Unary

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Algebra poSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Variable Ty rawPoSemiring
  open import Generic.Linear.Environment Ty poSemiring

  record FromLVar {ℓ} (_𝓥_ : Scoped ℓ) : Set (suc 0ℓ ⊔ ℓ) where
    field fromLVar : ∀ {A} → ∀[ _∋ A ⇒ _𝓥 A ]

    extendˡ : ∀ {RΘ s Γ} → [ _𝓥_ ] ctx {s} 0* Γ ++ᶜ RΘ ⇒ᵉ RΘ
    extendˡ .M = [ 0ᴹ │ 1ᴹ ]
    extendˡ .asLinRel = [ 0AsLinRel │ idAsLinRel ]AsLinRel
    extendˡ .sums = ⊴*-refl , ⊴*-refl
    extendˡ .lookup (sp0 , le) (lvar i q b) =
      fromLVar (lvar (↘ i) q (sp0 ++₂ ⊴*-trans le b))

    extendʳ : ∀ {RΘ s Γ} → [ _𝓥_ ] RΘ ++ᶜ ctx {s} 0* Γ ⇒ᵉ RΘ
    extendʳ .M = [ 1ᴹ │ 0ᴹ ]
    extendʳ .asLinRel = [ idAsLinRel │ 0AsLinRel ]AsLinRel
    extendʳ .sums = ⊴*-refl , ⊴*-refl
    extendʳ .lookup (le , sp0) (lvar i q b) =
      fromLVar (lvar (↙ i) q (⊴*-trans le b ++₂ sp0))

  open FromLVar {{...}} public

  instance
    flv^LVar : FromLVar _∋_
    flv^LVar .fromLVar v = v
