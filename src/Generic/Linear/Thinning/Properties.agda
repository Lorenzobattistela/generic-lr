{-# OPTIONS --safe --without-K #-}

open import Algebra.Core
import Algebra.Definitions as Defs
open import Function.Base using (flip; _∘_)
open import Level using (0ℓ)
open import Relation.Binary using (Rel; IsPreorder; Reflexive; Transitive)

module Generic.Linear.Thinning.Properties
  (Ty Ann : Set) (_⊴_ : Rel Ann 0ℓ)
  (0# : Ann) (_+_ : Op₂ Ann) (1# : Ann) (_*_ : Op₂ Ann)
  (let module ⊴ = Defs _⊴_)
  (let module ⊵ = Defs (flip _⊴_))
  (open ⊴ using (Congruent₂; Interchangable))
  -- ⊴:
  (⊴-refl : Reflexive _⊴_)
  (⊴-trans : Transitive _⊴_)
  -- +:
  (+-mono : Congruent₂ _+_)
  (+-identity-→ : ⊴.Identity 0# _+_)
  (+-identity-← : ⊵.Identity 0# _+_)
  (+-interchange : Interchangable _+_ _+_)
  -- ↑ Note: interchange + identity gives rise to assoc and comm.
  -- *:
  (*-mono : Congruent₂ _*_)
  (*-identityˡ-→ : ⊴.LeftIdentity 1# _*_)
  (*-identityʳ-← : ⊵.RightIdentity 1# _*_)
  (*-assoc-→ : ⊴.Associative _*_)
  -- both:
  (zeroˡ-→ : ∀ a → (0# * a) ⊴ 0#)
  (distribˡ-→ : ∀ a b c → ((a + b) * c) ⊴ ((a * c) + (b * c)))
  (zeroʳ-← : ∀ a → 0# ⊴ (a * 0#))
  (distribʳ-← : ∀ a b c → ((a * b) + (a * c)) ⊴ (a * (b + c)))
  -- ↑ Note: stdlib (and common mathematical) names for left/right
  -- distributivity are the wrong way round. I fix this.
  where

  open import Data.Product
  open import Data.Sum
  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Data.LTree.Matrix.Properties
  open Ident 0# 1#
  open Mult 0# _+_ _*_

  open import Generic.Linear.Operations _⊴_ 0# _+_ 1# _*_
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Environment Ty Ann _⊴_ 0# _+_ 1# _*_
  open import Generic.Linear.Thinning Ty Ann _⊴_ 0# _+_ 1# _*_

  open _─Env

  private
    variable
      PΓ QΔ RΘ : Ctx
      T : Ctx → Set
      𝓥 : Scoped
      s t u : LTree
      P Q R : Vector Ann s
      A : Ty

  -- TODO: refactor
  ⊴*-refl : P ⊴* P
  ⊴*-refl .get i = ⊴-refl
  ⊴*-trans : P ⊴* Q → Q ⊴* R → P ⊴* R
  ⊴*-trans PQ QR .get i = ⊴-trans (PQ .get i) (QR .get i)
  open Reflᴹ _⊴_ ⊴-refl renaming (reflᴹ to ⊴ᴹ-refl)
  open Transᴹ _⊴_ ⊴-trans renaming (transᴹ to ⊴ᴹ-trans)

  -- The rows of a thinning's matrix are a selection of standard basis vectors
  -- (i.e, rows from the identity matrix).
  -- Which rows, exactly, is defined by the action of the thinning (lookup).
  thinning-sub-1ᴹ :
    ∀ {PΓ QΔ A}
    (th : Thinning PΓ QΔ) (v : Var A (Ctx.Γ PΓ)) →
    M th (v .idx) ⊴* 1ᴹ (th .lookup v .idx)
  thinning-sub-1ᴹ {ctx {[-]} P Γ} {ctx {t} Q Δ} th v@(var here q) =
    th .lookup v .basis
  thinning-sub-1ᴹ {PΓ} th (var (go-left i) q) =
    thinning-sub-1ᴹ
      {leftᶜ (ctx→sctx PΓ)}
      record { M = topᴹ (th .M); sums = ⊴*-refl; lookup = th .lookup ∘ leftᵛ }
      (var i q)
  thinning-sub-1ᴹ {PΓ} th (var (go-right i) q) =
    thinning-sub-1ᴹ
      {rightᶜ (ctx→sctx PΓ)}
      record { M = botᴹ (th .M); sums = ⊴*-refl; lookup = th .lookup ∘ rightᵛ }
      (var i q)

  identity : Thinning PΓ PΓ
  M identity = 1ᴹ
  sums (identity {PΓ}) .get j = *ᴹ-1ᴹ (row (Ctx.R PΓ)) .get here j
    where
    open MultIdent 0# 1# (flip _⊴_) 0# _+_ _*_ ⊴-refl (flip ⊴-trans)
                   +-mono +-identity-← *-identityʳ-← zeroʳ-←
  idx (lookup identity v) = idx v
  tyq (lookup identity v) = tyq v
  basis (lookup identity v) = ⊴*-refl

  select : Thinning PΓ QΔ → (QΔ ─Env) 𝓥 RΘ → (PΓ ─Env) 𝓥 RΘ
  M (select th ρ) = M th *ᴹ M ρ
  sums (select {PΓ = PΓ} {QΔ} th ρ) =
    ⊴*-trans (sums ρ)
             (unrow-cong₂ (⊴ᴹ-trans (*ᴹ-cong (row-cong₂ (sums th)) ⊴ᴹ-refl)
                                    (*ᴹ-*ᴹ-→ (row (Ctx.R PΓ)) (M th) (M ρ))))
    where
    open Mult-cong 0# _+_ _*_ _⊴_ _⊴_ _⊴_ ⊴-refl +-mono *-mono
    open MultMult _⊴_ 0# _+_ 0# _+_ 0# _+_ _*_ _*_ _*_ _*_ ⊴-refl ⊴-trans
                  +-mono (+-identity-→ .proj₁ 0#) (+-identity-← .proj₂ 0#)
                  +-interchange *-assoc-→
                  zeroˡ-→ (λ a b c → distribˡ-→ b c a)
                  zeroʳ-← distribʳ-←
  lookup (select {𝓥 = 𝓥} {RΘ = ctx R Θ} th ρ) v =
    𝓥-psh (⊴*-trans (unrow-cong₂ (*ᴹ-cong
                                    (row-cong₂ (thinning-sub-1ᴹ th v))
                                    ⊴ᴹ-refl))
                    (mk λ j → 1ᴹ-*ᴹ (M ρ) .get (th .lookup v .idx) j))
          (lookup ρ (plain-var (lookup th v)))
    where
    postulate 𝓥-psh : ∀ {Γ : Vector Ty s} {P Q} →
                      Q ⊴* P → 𝓥 A (ctx P Γ) → 𝓥 A (ctx Q Γ)
    open Mult-cong 0# _+_ _*_ _⊴_ _⊴_ _⊴_ ⊴-refl +-mono *-mono
    open IdentMult 0# 1# _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans
                   +-mono +-identity-→ *-identityˡ-→ zeroˡ-→

  extend : ∀ {QΔ} → Ctx.R QΔ ⊴* 0* → Thinning PΓ (PΓ ++ᶜ QΔ)
  M (extend les) i (go-left j) = 1ᴹ i j
  M (extend les) i (go-right j) = 0#
  sums (extend les) .get (go-left j) = *ᴹ-1ᴹ (row _) .get here j
    where
    open MultIdent 0# 1# (flip _⊴_) 0# _+_ _*_ ⊴-refl (flip ⊴-trans)
                   +-mono +-identity-← *-identityʳ-← zeroʳ-←
  sums (extend {PΓ} {QΔ} les) .get (go-right j) =
    ⊴-trans (les .get j) (*ᴹ-0ᴹ (row (Ctx.R PΓ)) .get here j)
    where
    open MultZero 0# (flip _⊴_) 0# _+_ _*_ ⊴-refl (flip ⊴-trans)
                  +-mono (+-identity-← .proj₂ 0#) zeroʳ-←
  idx (lookup (extend les) v) = go-left (idx v)
  tyq (lookup (extend les) v) = tyq v
  basis (lookup (extend les) v) .get (go-left j) = ⊴-refl
  basis (lookup (extend les) v) .get (go-right j) = ⊴-refl

  extract : ∀[ □ T ⇒ T ]
  extract t = t identity

  duplicate : ∀[ □ T ⇒ □ (□ T) ]
  duplicate t ρ σ = t (select ρ σ)

  th^□ : Thinnable (□ T)
  th^□ = duplicate
