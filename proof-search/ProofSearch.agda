module ProofSearch where

open import Data.Nat

-- trans≤ : ∀ {m n o} → (m ≤ n) → (n ≤ o) → (m ≤ o)
-- trans≤ z≤n q = z≤n
-- trans≤ (s≤s P) (s≤s Q) = s≤s (trans≤ P Q)
-- 
-- n≤sn : (n : ℕ) → (n ≤ (suc n))
-- n≤sn zero = z≤n
-- n≤sn (suc N) = s≤s (n≤sn N)
-- 
-- m≤n+m : (m : ℕ) → (n : ℕ) → (m ≤ (n + m))
-- m≤n+m zero n = z≤n
-- m≤n+m (suc M) zero = s≤s (m≤n+m M zero)
-- m≤n+m (suc M) (suc N) = s≤s (trans≤ (n≤sn M) (m≤n+m (suc M) N))

m≤m+n : (m : ℕ) → (n : ℕ) → (m ≤ (m + n))
m≤m+n zero n = z≤n
m≤m+n (suc M) n = s≤s (m≤m+n M n)

n≤n² : (n : ℕ) → (n ≤ (n * n))
n≤n² zero = z≤n
n≤n² (suc N) = m≤m+n (suc N) (N * (suc N))
