\begin{code}
open import Prelims
open import Grammar

module Grammar.Substitution (G : Grammar) where
  open Grammar.Grammar G

  substitution : OpFamily
  substitution = record { 
    liftFamily = proto-substitution ; 
    isOpFamily = record { 
      comp = _•_ ; 
      apV-comp = refl ; 
      liftOp-comp = Sub↑-comp } }

  open OpFamily substitution using (assoc) renaming (liftOp-idOp to Sub↑-idOp;ap-idOp to sub-idOp;ap-comp to sub-comp;ap-congl to sub-cong;unitl to sub-unitl;unitr to sub-unitr) public
\end{code}

