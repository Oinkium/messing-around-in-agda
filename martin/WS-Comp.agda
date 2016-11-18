module WS-Comp where
-- in which we define a procedure turning strategies into core proofs
-- this yields the unique core proof with the same semantics as the
-- given strategy.

open import Function
open import Data.Sum as DS
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Nat renaming (_+_ to _+'_)
open import Data.Empty

open import WS-Syn
open import Game renaming (_⊗_ to _⊗'_ ; _⊘_ to _⊘'_)
open import WS-Sem-Fsc

-- Reversed semantics of various rules

⟦≈1⟧+ : (Γ : Ctx) → ⟦ Γ ⟧+ I ≈ I
⟦≈1⟧+ ε               = id≈
⟦≈1⟧+ (_,_ { + } M Γ) = (⟦ Γ ⟧≈+ dist01) ≈∘≈ (⟦≈1⟧+ Γ)
⟦≈1⟧+ (_,_ { - } P Γ) = (⟦ Γ ⟧≈+ dist02) ≈∘≈ (⟦≈1⟧+ Γ)

un⟦P⊕⟧ : ∀{Γ P Q} → Strat + ⟦ P ⊕ Q , Γ ⟧' → Strat + ⟦ P , Γ ⟧' ⊎ Strat + ⟦ Q , Γ ⟧'
un⟦P⊕⟧ {Γ} {P} {Q} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ [ P ⊕ Q ]' Γ | ⟦,Δ⟧≡⟦Δ⟧+ [ P ]' Γ | ⟦,Δ⟧≡⟦Δ⟧+ [ Q ]' Γ
   = coprod $ σ ∘≈ distΓ+ Γ

un⟦P⊕ω⟧ : ∀{Γ P} → Strat + ⟦ ω⊕ P , Γ ⟧' → ℕ × (Strat + ⟦ P , Γ ⟧')
un⟦P⊕ω⟧ {Γ} {P} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ [ ω⊕ P ]' Γ | ⟦,Δ⟧≡⟦Δ⟧+ [ P ]' Γ 
   = coprodω $ σ ∘≈ distΓ+ω Γ

un⟦P⅋⟧ : ∀{Γ P Q} → Strat + ⟦ P ⅋ Q , Γ ⟧'
          → Strat + ⟦ P , Q , Γ ⟧' ⊎ Strat + ⟦ Q , P , Γ ⟧'
un⟦P⅋⟧ {Γ} {P} {Q} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ [ P ⅋ Q ]' Γ | ⟦,Δ⟧≡⟦Δ⟧+ (P , Q , ε) Γ | ⟦,Δ⟧≡⟦Δ⟧+ (Q , P , ε) Γ
   = coprod $ σ ∘≈ ⟦ Γ ⟧≈+ dec1 ∘≈ distΓ+ Γ

un⟦P⊗1⟧ :  ∀ {Γ M N} → Strat - ⟦ M ⊗ N , Γ ⟧' → Strat - ⟦ M , N , Γ ⟧'
un⟦P⊗1⟧ {Γ} {M} {N} σ rewrite ⟦,Δ⟧≡⟦Δ⟧- [ M ⊗ N ]' Γ | ⟦,Δ⟧≡⟦Δ⟧- (M , N , ε) Γ = pi1 $ distΓ- Γ ≈∘ ⟦ Γ ⟧≈- dec1 ≈∘ σ

un⟦P⊗2⟧ :  ∀ {Γ M N} → Strat - ⟦ M ⊗ N , Γ ⟧' → Strat - ⟦ N , M , Γ ⟧'
un⟦P⊗2⟧ {Γ} {M} {N} σ rewrite ⟦,Δ⟧≡⟦Δ⟧- [ M ⊗ N ]' Γ | ⟦,Δ⟧≡⟦Δ⟧- (N , M , ε) Γ = pi2 $ distΓ- Γ ≈∘ ⟦ Γ ⟧≈- dec1 ≈∘ σ

un⟦P&1⟧ : ∀ {Γ M N} → Strat - ⟦ M & N , Γ ⟧' → Strat - ⟦ M , Γ ⟧'
un⟦P&1⟧ {Γ} {M} {N} σ rewrite ⟦,Δ⟧≡⟦Δ⟧- [ M & N ]' Γ | ⟦,Δ⟧≡⟦Δ⟧- [ M ]' Γ = pi1 $ distΓ- Γ ≈∘ σ

un⟦P&2⟧ : ∀ {Γ M N} → Strat - ⟦ M & N , Γ ⟧' → Strat - ⟦ N , Γ ⟧'
un⟦P&2⟧ {Γ} {M} {N} σ rewrite ⟦,Δ⟧≡⟦Δ⟧- [ M & N ]' Γ | ⟦,Δ⟧≡⟦Δ⟧- [ N ]' Γ = pi2 $ distΓ- Γ ≈∘ σ

un⟦P&ω⟧ : ∀ {Γ M} → ℕ → Strat - ⟦ ω& M , Γ ⟧' → Strat - ⟦ M , Γ ⟧'
un⟦P&ω⟧ {Γ} {M} n σ rewrite ⟦,Δ⟧≡⟦Δ⟧- [ ω& M ]' Γ | ⟦,Δ⟧≡⟦Δ⟧- [ M ]' Γ = pin n $ distΓ-ω Γ ≈∘ σ

un⟦P⊥⊘⟧ : ∀ {Γ} {P : Fml +} {N} → Strat - ⟦ F⊥ , P , N , Γ ⟧' → Strat - ⟦ F⊥ , P ⊘ N , Γ ⟧'
un⟦P⊥⊘⟧ {Γ} {P} {N} σ rewrite ⟦,Δ⟧≡⟦Δ⟧- (F⊥ , P , N , ε) Γ | ⟦,Δ⟧≡⟦Δ⟧- (F⊥ , P ⊘ N , ε) Γ = ⟦ Γ ⟧≈- (lfe' ^-1) ≈∘ σ

un⟦P⊤◁⟧ : ∀ {Γ} {N : Fml - } {P} → Strat + ⟦ F⊤ , N , P , Γ ⟧' → Strat + ⟦ F⊤ , N ◁ P , Γ ⟧'
un⟦P⊤◁⟧ {Γ} {N} {P} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ (F⊤ , N , P , ε) Γ | ⟦,Δ⟧≡⟦Δ⟧+ (F⊤ , N ◁ P , ε) Γ = σ ∘≈ ⟦ Γ ⟧≈+ (lfe' ^-1)

un⟦P⊥⅋⟧ : ∀ {Γ P Q} → Strat - ⟦ F⊥ , P , Q , Γ ⟧' → Strat - ⟦ F⊥ , P ⅋ Q , Γ ⟧'
un⟦P⊥⅋⟧ {Γ} {P} {Q} σ rewrite ⟦,Δ⟧≡⟦Δ⟧- (F⊥ , P , Q , ε) Γ | ⟦,Δ⟧≡⟦Δ⟧- (F⊥ , P ⅋ Q , ε) Γ = ⟦ Γ ⟧≈- (pasc⊸ ≈∘≈ sym⊗ ≈⊸ o) ≈∘ σ

un⟦P⊤⊗⟧ : ∀ {Γ M N} → Strat + ⟦ F⊤ , M , N , Γ ⟧' → Strat + ⟦ F⊤ , M ⊗ N , Γ ⟧'
un⟦P⊤⊗⟧ {Γ} {M} {N} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ (F⊤ , M , N , ε) Γ | ⟦,Δ⟧≡⟦Δ⟧+ ( F⊤ , M ⊗ N , ε) Γ = σ ∘≈ ⟦ Γ ⟧≈+ (pasc⊸ ≈∘≈ sym⊗ ≈⊸ o)

un⟦P⊥+⟧ : ∀ {P : Fml + } → Strat - ⟦ F⊥ , P , ε ⟧' → Strat + ⟦ P , ε ⟧'
un⟦P⊥+⟧ σ = unσ⊸o (↑≈⊸o ^-1 ≈∘ σ)

un⟦P⊤-⟧ : ∀ {N : Fml - } → Strat + ⟦ F⊤ , N , ε ⟧' → Strat - ⟦ N , ε ⟧'
un⟦P⊤-⟧ σ = unσ⊸o (σ ∘≈ ↑≈⊸o ^-1)

un⟦P⊥-⟧ : ∀ {Γ} {N : Fml -} → Strat - ⟦ F⊥ , N , Γ ⟧' → Strat - ⟦ F⊥ , Γ ⟧'
un⟦P⊥-⟧ {Γ} {N} σ rewrite ⟦,Δ⟧≡⟦Δ⟧- (F⊥ , N , ε) Γ | ⟦,Δ⟧≡⟦Δ⟧- (F⊥ , ε) Γ = ⟦ Γ ⟧≈- abs ≈∘ σ

un⟦P⊤+⟧ : ∀ {Γ} {P : Fml + } → Strat + ⟦ F⊤ , P , Γ ⟧' → Strat + ⟦ F⊤ , Γ ⟧'
un⟦P⊤+⟧ {Γ} {P} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ (F⊤ , P , ε) Γ | ⟦,Δ⟧≡⟦Δ⟧+ (F⊤ , ε) Γ = σ ∘≈ ⟦ Γ ⟧≈+ abs


-- A Dom Γ will represent a proof that reify terminates for input σ : ⟦ ⊢ Γ ⟧

data Dom : ∀ {p}(Γ : Seq p) → Set where
  DF0   : ∀ {Γ} → Dom (F0 , Γ)
  DF1   : ∀ {Γ} → Dom (F1 , Γ)
  DF⊥   : Dom (F⊥ , ε)
  DF⊤   : Dom (F⊤ , ε)
  D⊥NΓ  : ∀ {Γ} {N} → Dom (F⊥ , Γ)          → Dom (F⊥ , N , Γ)
  D⊥Pε  : ∀ {P}     → Dom (P , ε)           → Dom (F⊥ , P , ε)
  D⊥PQΓ : ∀ {Γ P Q} → Dom (F⊥ , P ⅋ Q , Γ) → Dom (F⊥ , P , Q , Γ)
  D⊥PMΓ : ∀ {Γ P M} → Dom (F⊥ , P ⊘ M , Γ) → Dom (F⊥ , P , M , Γ)
  D⊤PΓ  : ∀ {Γ} {P} → Dom (F⊤ , Γ)         → Dom (F⊤ , P , Γ)
  D⊤Nε  : ∀ {N}     → Dom (N , ε)          → Dom (F⊤ , N , ε)
  D⊤NQΓ : ∀ {Γ N Q} → Dom (F⊤ , N ◁ Q , Γ) → Dom (F⊤ , N , Q , Γ)
  D⊤NMΓ : ∀ {Γ N M} → Dom (F⊤ , N ⊗ M , Γ) → Dom (F⊤ , N , M , Γ)
  DM⊗NΓ : ∀ {Γ M N} → Dom (M , N , Γ) → Dom (N , M , Γ) → Dom (M ⊗ N , Γ)
  DP⅋QΓ : ∀ {Γ P Q} → Dom (P , Q , Γ) → Dom (Q , P , Γ) → Dom (P ⅋ Q , Γ)
  DP⊕QΓ : ∀ {Γ P Q} → Dom (P , Γ)     → Dom (Q , Γ)     → Dom (P ⊕ Q , Γ)
  Dω⊕PΓ : ∀ {Γ P}   → Dom (P , Γ)     → Dom (ω⊕ P , Γ)
  DM&NΓ : ∀ {Γ M N} → Dom (M , Γ)     → Dom (N , Γ)     → Dom (M & N , Γ)
  Dω&MΓ : ∀ {Γ M}   → Dom (M , Γ)     → Dom (ω& M , Γ)
  DA⊘MΓ : ∀ {Γ}{p}{A : Fml p}{M} → Dom (A , M , Γ) → Dom (A ⊘ M , Γ)
  DA◁PΓ : ∀ {Γ}{p}{A : Fml p}{P} → Dom (A , P , Γ) → Dom (A ◁ P , Γ)

reif  : ∀ {p}{Γ : Seq p}(h : Dom Γ) → Strat p ⟦ Γ ⟧' → ⊢ Γ
reif  (DF0{Γ}) σ = f (subst (Strat +) (sym $ ⟦Δ⟧+⟦P⟧≡⟦P,Δ⟧ Γ) σ ∘≈ ⟦≈1⟧+ Γ)
  where f : Strat + I → ⊢ F0 , Γ
        f (pos () f)
reif DF⊥            σ = ⊥-elim (noσo σ)
reif DF1            σ = P1
reif DF⊤            σ = P⊤
reif (D⊥NΓ {Γ} h)   σ = P⊥-  $ reif h $ un⟦P⊥-⟧ {Γ} σ
reif (D⊥Pε {P} h)   σ = P⊥+  $ reif h $ un⟦P⊥+⟧ {P} σ
reif (D⊥PQΓ{Γ} h)   σ = P⊥⅋  $ reif h $ un⟦P⊥⅋⟧ {Γ} σ
reif (D⊥PMΓ{Γ} h)   σ = P⊥⊘  $ reif h $ un⟦P⊥⊘⟧ {Γ} σ 
reif (D⊤PΓ {Γ} h)   σ = P⊤+  $ reif h $ un⟦P⊤+⟧ {Γ} σ
reif (D⊤Nε {N} h)   σ = P⊤-  $ reif h $ un⟦P⊤-⟧ {N} σ
reif (D⊤NQΓ{Γ} h)   σ = P⊤◁  $ reif h $ un⟦P⊤◁⟧{Γ} σ
reif (D⊤NMΓ{Γ} h)   σ = P⊤⊗  $ reif h $ un⟦P⊤⊗⟧{Γ} σ
reif (DM⊗NΓ{Γ} h g) σ = P⊗  ( reif h $ un⟦P⊗1⟧{Γ} σ) $ reif g $ un⟦P⊗2⟧{Γ} σ 
reif (DP⅋QΓ{Γ} h g) σ = [ P⅋₁ ∘ reif h , P⅋₂ ∘ reif g ]′ $ un⟦P⅋⟧{Γ} σ 
reif (DP⊕QΓ{Γ} h g) σ = [ P⊕₁ ∘ reif h , P⊕₂ ∘ reif g ]′ ( un⟦P⊕⟧{Γ} σ)
reif (Dω⊕PΓ{Γ} h)   σ = P⊕ω (proj₁ p) (reif h $ proj₂ p)
                            where p = un⟦P⊕ω⟧{Γ} σ
reif (DM&NΓ{Γ} h g) σ = P&  ( reif h $ un⟦P&1⟧{Γ} σ) $ reif g $ un⟦P&2⟧{Γ} σ
reif (Dω&MΓ{Γ} h)   σ = P&ω  (λ n → reif h $ un⟦P&ω⟧{Γ} n σ)
reif (DA⊘MΓ    h)   σ = P⊘ (reif h σ)
reif (DA◁PΓ    h)   σ = P◁ (reif h σ)


-- We now seek to construct ∀ Γ → Dom Γ, showing that reify terminates.
-- We will do this by induction on the total size of a sequent.

open import Data.Nat renaming (_+_ to _+'_)
open import Data.Product
open import Data.Nat.Properties

fsize : ∀ {p} → Fml p → ℕ
fsize F0 = suc zero
fsize F1 = suc zero
fsize F⊤ = suc zero
fsize F⊥ = suc zero
fsize (M ⊗ N) = suc (_+'_ (fsize M) (fsize N))
fsize (P ⅋ Q) = suc (_+'_ (fsize P) (fsize Q))
fsize (P ⊕ Q) = suc (_+'_ (fsize P) (fsize Q))
fsize (M & N) = suc (_+'_ (fsize M) (fsize N))
fsize (A ⊘ M) = suc (_+'_ (fsize A) (fsize M))
fsize (A ◁ P) = suc (_+'_ (fsize A) (fsize P))
fsize (ω& M) = suc (fsize M)
fsize (ω⊕ P) = suc (fsize P)

csize : Ctx → ℕ
csize ε = zero
csize (A , Γ) = suc (_+'_ (fsize A) (csize Γ))

size : ∀ {p} → Seq p → ℕ
size (A , Γ) = suc (_+'_ (fsize A) (csize Γ))

-- We need some properties of natural numbers

open import Algebra.Structures
open IsCommutativeSemiring isCommutativeSemiring using (+-assoc ; +-comm)

+lem1 : ∀ x {y z} → suc(x +' suc (y +' z)) ≡ suc(suc (x +' y +' z))
+lem1 x {y} = cong suc (trans (+-comm x _) (cong suc (trans (+-comm (y +' _) _)
                                                     (sym (+-assoc x _ _)))))

≤lem1 : ∀ x {y z n} → suc(x +' suc (y +' z)) ≤ n → suc(suc (x +' y +' z)) ≤ n
≤lem1 x {n = n} = subst (_≥_ n) (+lem1 x)

≤lem2 : ∀ x {y z n} → suc(suc (x +' y +' z)) ≤ n → suc(x +' suc (y +' z)) ≤ n
≤lem2 x {n = n} = subst (_≥_ n) (sym (+lem1 x))

≤lem3 : ∀ x {y z n} → suc(suc (x +' y +' z)) ≤ n → suc(y +' suc (x +' z)) ≤ n
≤lem3 x {y}{z}{n} = subst (_≥_ n)
  (cong suc (trans (cong (flip _+'_ z) (+-comm (suc x) _))
                   (+-assoc y (suc x) _)))

≤refl : ∀ {x} → x ≤ x
≤refl {x} = DecTotalOrder.refl decTotalOrder {x}

≤trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤trans {x} = DecTotalOrder.trans decTotalOrder {x}

≤lem4 : ∀ x {y z n} → suc(suc (x +' y +' z)) ≤ n → suc(x +' z) ≤ n
≤lem4 x {y} = <-trans (s≤s (m≤m+n x y +-mono ≤refl))

≤lem5 : ∀ x {y z n} → suc(suc (x +' y +' z)) ≤ n → suc(y +' z) ≤ n
≤lem5 x {y} = <-trans (s≤s (n≤m+n x y +-mono ≤refl))

≤lem6 : ∀ {x y} z → suc (z +' x) ≤ y → x ≤ y
≤lem6 {x} {zero} z ()
≤lem6 {x} {suc n} z (s≤s m≤n) = ≤trans {x} {n} {suc n} (≤trans {x} {z +' x} {n} (n≤m+n z x) m≤n) (n≤m+n 1 n)

sucinj : ∀ {m n} → suc m ≡ suc n → m ≡ n
sucinj refl = refl

-- We now construct Dom Γ by induction on (an upper bound of) the size
-- of Γ.

-- This involves an 'inner induction' on context length.

ctlen : Ctx → ℕ
ctlen ε = 0
ctlen (y , y') = suc (ctlen y')

dom : ∀ {p}{A : Fml p}{Γ n} → size(A , Γ) ≤ n → Dom(A , Γ)
dom {.+} {F0} le = DF0
dom {.-} {F1} le = DF1
dom {.-} {F⊥} (s≤s (s≤s le)) = dom⊥ _ _ _ refl le
  where dom⊥ : ∀ c Γ n → c ≡ ctlen Γ → csize(Γ) ≤ n → Dom (F⊥ , Γ) -- induction on length of Gamma (c)
        dom⊥ zero ε n refl le' = DF⊥
        dom⊥ zero (A , Γ) n () le'
        dom⊥ (suc zero) ε n' () le'
        dom⊥ (suc zero) (_,_ { - } A ε) n' refl le' = D⊥NΓ DF⊥
        dom⊥ (suc zero) (_,_ { + } A ε) n' refl le' = D⊥Pε (dom le')
        dom⊥ (suc zero) (y , y' , y0) n' () le'
        dom⊥ (suc (suc n)) ε n' () le'
        dom⊥ (suc (suc n)) (y , ε) n' () le'
        dom⊥ (suc (suc n)) (_,_ { - } M Γ) n' eq le' = D⊥NΓ (dom⊥ (suc n) Γ n' (sucinj eq) (≤lem6 (fsize M) le'))
        dom⊥ (suc (suc n)) (_,_ {+} P (_,_ { - } A Γ)) n' eq le' = D⊥PMΓ (dom⊥ (suc n) (P ⊘ A , Γ) n' (sucinj eq) (≤lem1 (fsize P) le'))
        dom⊥ (suc (suc n)) (_,_ {+} P (_,_ { + } A Γ)) n' eq le' = D⊥PQΓ (dom⊥ (suc n) (P ⅋ A , Γ) n' (sucinj eq) (≤lem1 (fsize P) le'))
dom {.+} {F⊤} (s≤s (s≤s le)) = dom⊤ _ _ _ refl le
  where dom⊤ : ∀ c Γ n → c ≡ ctlen Γ → csize(Γ) ≤ n → Dom (F⊤ , Γ) -- induction on length of Gamma (c)
        dom⊤ zero ε n refl le' = DF⊤
        dom⊤ zero (A , Γ) n () le'
        dom⊤ (suc zero) ε n' () le'
        dom⊤ (suc zero) (_,_ { + } A ε) n' refl le' = D⊤PΓ DF⊤
        dom⊤ (suc zero) (_,_ { - } A ε) n' refl le' = D⊤Nε (dom le')
        dom⊤ (suc zero) (y , y' , y0) n' () le'
        dom⊤ (suc (suc n)) ε n' () le'
        dom⊤ (suc (suc n)) (y , ε) n' () le'
        dom⊤ (suc (suc n)) (_,_ { + } P Γ) n' eq le' = D⊤PΓ (dom⊤ (suc n) Γ n' (sucinj eq) (≤lem6 (fsize P) le'))
        dom⊤ (suc (suc n)) (_,_ { - } N (_,_ { - } A Γ)) n' eq le' = D⊤NMΓ (dom⊤ (suc n) (N ⊗ A , Γ) n' (sucinj eq) (≤lem1 (fsize N) le'))
        dom⊤ (suc (suc n)) (_,_ { - } N (_,_ { + } A Γ)) n' eq le' = D⊤NQΓ (dom⊤ (suc n) (N ◁ A , Γ) n' (sucinj eq) (≤lem1 (fsize N) le'))
dom {A = M ⊗ N} le = DM⊗NΓ (dom (≤lem2 (fsize M) le)) (dom (≤lem3 (fsize M) le))
dom {A = P ⅋ Q} le = DP⅋QΓ (dom (≤lem2 (fsize P) le)) (dom (≤lem3 (fsize P) le))
dom {A = P ⊕ Q} le = DP⊕QΓ (dom (≤lem4 (fsize P) le)) (dom (≤lem5 (fsize P) le))
dom {A = M & N} le = DM&NΓ (dom (≤lem4 (fsize M) le)) (dom (≤lem5 (fsize M) le))
dom {A = A ⊘ M} le = DA⊘MΓ (dom (≤lem2 (fsize A) le))
dom {A = A ◁ P} le = DA◁PΓ (dom (≤lem2 (fsize A) le))
dom {A = ω& M} (s≤s le) = Dω&MΓ (dom le)
dom {A = ω⊕ P} (s≤s le) = Dω⊕PΓ (dom le)


allDom : ∀ {p}(Γ : Seq p) → Dom Γ
allDom (A , Γ) = dom (DecTotalOrder.refl decTotalOrder)

-- And can hence produce an (unqualified) reify:

reify : ∀ {p}{Γ : Seq p} → Strat p ⟦ Γ ⟧' → ⊢ Γ
reify {p}{Γ} = reif (allDom Γ)

-- We can use reify for reduction-free normalisation of proofs to core
-- proofs:

open import WS-Sem

nbe : ∀ {p}{Γ : Seq p} → ⊢ Γ → ⊢ Γ
nbe p = reify ⟦ p ⟧⊢ 

-- It is the case that nbe p is the unique core proof with the same
-- semantics of p, where "core proof" means using only the rules used
-- in reify.
