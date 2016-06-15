\begin{code}
open import Grammar.Base
module Reduction.Botsub (G : Grammar) (R : Grammar.Reduction G) where
open import Grammar G
open import Reduction.Base G R

botsub₃-red : ∀ {V} {K1} {K2} {K3} 
              {M1 M1' : Expression V (varKind K1)} {M2 M2' : Expression V (varKind K2)} {M3 M3' : Expression V (varKind K3)} →
              M1 ↠ M1' → M2 ↠ M2' → M3 ↠ M3' → _↠s_ SUB (x₂:= M1 ,x₁:= M2 ,x₀:= M3) (x₂:= M1' ,x₁:= M2' ,x₀:= M3')
botsub₃-red _ _ M3↠M3' _ x₀ = M3↠M3'
botsub₃-red _ M2↠M2' _ _ (↑ x₀) = M2↠M2'
botsub₃-red M1↠M1' _ _ _ (↑ (↑ x₀)) = M1↠M1'
botsub₃-red _ _ _ _ (↑ (↑ (↑ _))) = ref

--TODO General botsub n
\end{code}
