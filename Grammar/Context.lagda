\begin{code}
module Grammar.Context where

data Context (K : VarKind) : Alphabet → Set where
  〈〉 : Context K ∅
  _,_ : ∀ {V} → Context K V → Expression V (parent K) → Context K (V , K)

typeof : ∀ {V} {K} (x : Var V K) (Γ : Context K V) → Expression V (parent K)
typeof x₀ (_ , A) = A 〈 upRep 〉
typeof (↑ x) (Γ , _) = typeof x Γ 〈 upRep 〉

data Context' (A : Alphabet) (K : VarKind) : ℕ → Set where
  〈〉 : Context' A K zero
  _,_ : ∀ {F} → Context' A K F → Expression (extend A K F) (parent K) → Context' A K (suc F)
    
typeof' : ∀ {A} {K} {F} → Fin F → Context' A K F → Expression (extend A K F) (parent K)
typeof' zero (_ , A) = A 〈 upRep 〉
typeof' (suc x) (Γ , _) = typeof' x Γ 〈 upRep 〉
\end{code}
