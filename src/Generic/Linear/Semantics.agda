{-# OPTIONS --safe --sized-types --without-K --prop --postfix-projections #-}

open import Algebra.Po
open import Level using (Level; 0ℓ; _⊔_; suc)

module Generic.Linear.Semantics
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open PoSemiring poSemiring
    renaming (Carrier to Ann
             ; _≤_ to _⊴_
             ; refl to ⊴-refl; trans to ⊴-trans
             )

  open import Algebra.Po.Relation
  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Data.Product
  open import Data.Wrap
  open import Function using (Equivalence)
  open import Size
  open import Relation.Unary
  open import Relation.Unary.Bunched

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Algebra poSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Syntax.Interpretation Ty rawPoSemiring
  open import Generic.Linear.Syntax.Interpretation.Map Ty poSemiring
  open import Generic.Linear.Syntax.Term Ty rawPoSemiring
  open import Generic.Linear.Variable Ty rawPoSemiring
  open import Generic.Linear.Environment Ty poSemiring
  open import Generic.Linear.Renaming Ty poSemiring
  open import Generic.Linear.Renaming.Properties Ty poSemiring
  open import Generic.Linear.Environment.Properties Ty poSemiring

  private
    variable
      A : Ty
      ℓ v c : Level
      fl : PremisesFlags
      𝓥 : Scoped v
      𝓒 : Scoped c
      RΘ : Ctx

  Kripke : (𝓥 : Scoped v) (𝓒 : Scoped c) (PΓ : Ctx) (A : Ty) →
           Ctx → Set _
  Kripke = Wrap λ 𝓥 𝓒 PΓ A → □ʳ (([ 𝓥 ]_⇒ᵉ PΓ) ─✴ᶜ 𝓒 A)

  mapK𝓒 : ∀ {v c c′} {𝓥 : Scoped v} {𝓒 : Scoped c} {𝓒′ : Scoped c′} →
          (∀ {A} → ∀[ 𝓒 A ⇒ 𝓒′ A ]) →
          ∀ {PΓ A} → ∀[ Kripke 𝓥 𝓒 PΓ A ⇒ Kripke 𝓥 𝓒′ PΓ A ]
  mapK𝓒 f b .get th .app✴ sp ρ = f (b .get th .app✴ sp ρ)

  record Semantics (d : System fl) (𝓥 : Scoped v) (𝓒 : Scoped c)
                   : Set (suc 0ℓ ⊔ v ⊔ c) where
    field
      ren^𝓥 : Renameable (𝓥 A)
      var : ∀[ 𝓥 A ⇒ 𝓒 A ]
      alg : ∀[ ⟦ d ⟧s (Kripke 𝓥 𝓒) A ⇒ 𝓒 A ]

    psh^𝓥 : IsPresheaf 𝓥
    psh^𝓥 = ren⇒psh (λ {A} → ren^𝓥 {A})
    open With-psh^𝓥 psh^𝓥

    [_]_⇒ᶜ_ : (𝓒 : Scoped ℓ) (PΓ QΔ : Ctx) → Set ℓ
    [ 𝓒 ] PΓ ⇒ᶜ QΔ = ∀ {sz A} → Tm d sz A QΔ → 𝓒 A PΓ

    semantics : ∀ {PΓ QΔ} → [ 𝓥 ] PΓ ⇒ᵉ QΔ → [ 𝓒 ] PΓ ⇒ᶜ QΔ
    body : ∀ {PΓ QΔ sz} → [ 𝓥 ] PΓ ⇒ᵉ QΔ → ∀ {RΘ A} →
      Scope (Tm d sz) RΘ A QΔ → Kripke 𝓥 𝓒 RΘ A PΓ

    semantics ρ (`var v) = var (ρ .lookup (ρ .sums) v)
    semantics ρ (`con {sz = sz} t) =
      alg (map-s (ρ .M) d
        (λ r → body (record { [_]_⇒ᵉ_ ρ; sums = ρ .asLinRel .equiv .g r }))
        (sums-⊴* ρ) t)
      where open Equivalence

    body ρ t .get th .app✴ r σ =
      let ρ′ = ren^Env ren^𝓥 ρ th in
      semantics (++ᵉ (ρ′ ✴⟨ r ⟩ σ)) t
