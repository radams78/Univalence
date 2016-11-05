\AgdaHide{
\begin{code}
open import Grammar.Base

module Reduction.Meta (G : Grammar) where
open Grammar G

_⊆_ : Reduction → Reduction → Set
R ⊆ S = ∀ {V AA K} {c : Con (SK AA K)} {EE : ListAbs V AA} {F} → R c EE F → S c EE F

module Include (R S : Reduction) (R⊆S : R ⊆ S) where
  open import Reduction.Base G R as RedR
  open import Reduction.Base G S as RedS

  include-⇒ : ∀ {V C K} {E F : Subexp V C K} → E RedR.⇒ F → E RedS.⇒ F
  include-⇒ (RedR.redex {c} {EE} {F} E▷F) = RedS.redex (R⊆S E▷F)
  include-⇒ (RedR.app E⇒F) = RedS.app (include-⇒ E⇒F)
  include-⇒ (RedR.appl E⇒F) = RedS.appl (include-⇒ E⇒F)
  include-⇒ (RedR.appr E⇒F) = RedS.appr (include-⇒ E⇒F)
\end{code}
}
